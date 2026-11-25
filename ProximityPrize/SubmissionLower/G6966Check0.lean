import ProximityPrize.SubmissionLower.Low6966Gates
import ProximityPrize.SubmissionLower.Gate6966Fin

set_option Elab.async false

-- merged module G6966CheckOrders
section Merged_G6966CheckOrders
namespace Gate6966Fin
open K1_13 (Shape)
def gtOne (id t : ℕ) : Bool := (Low6966Gate.gateList id t).all fun p =>
  let x : Shape := ⟨p.1, p.2, t⟩
  let k : Low6966Allocation.Band := ⟨id % 34, Nat.mod_lt _ (by decide)⟩
  let l := Low6966Allocation.order (Low6966Allocation.bandOrders k) x
  Nat.blt 0 l && Nat.ble (Low6966Gate.gatePrice Gfun x l)
    (Low6966Allocation.allowance k ((Low6966Allocation.start k).t + t) p.1 p.2 t)


end Gate6966Fin

end Merged_G6966CheckOrders

-- merged module Witness6966Chunk
section Merged_Witness6966Chunk
set_option Elab.async false
set_option maxHeartbeats 3000000
set_option maxRecDepth 200000
namespace Gate6966Fin
open K1_13 (Shape shape)
open Low6966SharedPrice (additiveBase nonsharedFee)

/-- the `i`-th chunk of 32 shapes of a gate list, checked as a gate row -/
def chunkOf (l : List (ℕ × ℕ)) (i : ℕ) : List (ℕ × ℕ) := (l.drop (32 * i)).take 32

theorem all_of_chunks (f : ℕ × ℕ → Bool) (l : List (ℕ × ℕ)) (N : ℕ) (hN : l.length ≤ 32 * N)
    (h : ∀ i, i < N → (chunkOf l i).all f = true) : l.all f = true := by
  rw [List.all_eq_true]
  intro p hp
  obtain ⟨k, hk, hkp⟩ := List.getElem_of_mem hp
  have hi : k / 32 < N := by omega
  have := List.all_eq_true.mp (h (k / 32) hi) p ?_
  · exact this
  · unfold chunkOf
    rw [← hkp]
    have hmem : l[k] ∈ (l.drop (32 * (k / 32))).take 32 := by
      rw [List.mem_iff_getElem]
      refine ⟨k - 32 * (k / 32), ?_, ?_⟩
      · simp [List.length_take, List.length_drop]; omega
      · simp [List.getElem_take, List.getElem_drop]; congr 1; omega
    exact hmem

def oneF (_id t : ℕ) (p : ℕ × ℕ) : Bool := !(valid ⟨p.1, p.2, t⟩) || shapeOK ⟨p.1, p.2, t⟩

def gtF (id t : ℕ) (p : ℕ × ℕ) : Bool :=
  let x : Shape := ⟨p.1, p.2, t⟩
  let k : Low6966Allocation.Band := ⟨id % 34, Nat.mod_lt _ (by decide)⟩
  let l := Low6966Allocation.order (Low6966Allocation.bandOrders k) x
  Nat.blt 0 l && Nat.ble (Low6966Gate.gatePrice Gfun x l)
    (Low6966Allocation.allowance k ((Low6966Allocation.start k).t + t) p.1 p.2 t)

theorem one_of_chunks (id t N : ℕ) (hN : (Low6966Gate.gateList id t).length ≤ 32 * N)
    (h : ∀ i, i < N → (chunkOf (Low6966Gate.gateList id t) i).all (oneF id t) = true) : one id t = true :=
  all_of_chunks (oneF id t) _ N hN h

theorem gtOne_of_chunks (id t N : ℕ) (hN : (Low6966Gate.gateList id t).length ≤ 32 * N)
    (h : ∀ i, i < N → (chunkOf (Low6966Gate.gateList id t) i).all (gtF id t) = true) : gtOne id t = true :=
  all_of_chunks (gtF id t) _ N hN h
def hiTab : ℕ → List (List ℤ)
  | 1 => [[0, 39251835991215360, 155160962561491200], [39251835991215360, 149980979443347840, 795447676052641920], [155160962561491200, 795447676052641920, 2461153937333616000]]
  | 2 => [[0, 43765106196728640, 138697765881171840], [43765106196728640, 161606057188517280, 598684265902436160], [138697765881171840, 598684265902436160, 1810857692289280320]]
  | 3 => [[0, 34191490393196160, 103873744650748800], [34191490393196160, 200584350102899520, 666511629364518720], [103873744650748800, 666511629364518720, 2002133435035876800]]
  | 4 => [[0, 49252838423501760, 155160962561491200], [49252838423501760, 221141973957193440, 815449680917214720], [155160962561491200, 815449680917214720, 2461153937333616000]]
  | 5 => [[0, 961702793864192, 3023023622878464], [961702793864192, 1904171333531440, 6634038567368208], [3023023622878464, 6634038567368208, 20177946184676400]]
  | 6 => [[0, 992477277733344, 3141562368284064], [992477277733344, 1950333059335168, 6876815022280704], [3141562368284064, 6876815022280704, 20958706137010176]]
  | 7 => [[0, 653957955172672, 1963013660900544], [653957955172672, 3658316914073104, 11205759307181232], [1963013660900544, 11205759307181232, 33619557512308752]]
  | 8 => [[0, 653957955172672, 1963013660900544], [653957955172672, 4427679010801904, 13570835366494032], [1963013660900544, 13570835366494032, 40714785690247152]]
  | 9 => [[0, 751980383692768, 2257080946460832], [751980383692768, 4796972736093216, 14678716542367968], [2257080946460832, 14678716542367968, 44038429217868960]]
  | _ => []

def rayK (c : ℕ) (x : Shape) : Fin 3 → Fin 3 → ℤ := if isT c then rayT x else rayO x

/-- the gate's top ray as literals (checked equal to `savedK c (hiS (Gk c))` for 1 <= c <= 9) -/
def savedK (c : ℕ) (x : Shape) := if isT c then savedT x else savedO x

def hiL (c : ℕ) : Fin 3 → Fin 3 → ℤ := fun i k =>
  if c = 0 ∨ 10 ≤ c then savedK c (hiS (Gk c)) i k else ((hiTab c).getD i.1 []).getD k.1 0

theorem hiTab_ok : ∀ c, c < 10 → 1 ≤ c → ∀ i k : Fin 3,
    ((hiTab c).getD i.1 []).getD k.1 0 = savedK c (hiS (Gk c)) i k := by decide +kernel

theorem hiL_eq (c : ℕ) : hiL c = savedK c (hiS (Gk c)) := by
  funext i k
  unfold hiL
  by_cases h : c = 0 ∨ 10 ≤ c
  · simp only [h, ite_true]
  · rw [if_neg h]
    exact hiTab_ok c (by omega) (by omega) i k

theorem numK_eq (c : ℕ) (x : Shape) : numK c x = thNum (rayK c x) (hiL c) := by
  rw [hiL_eq]
  unfold numK rayK savedK
  by_cases h : isT c = true
  · simp only [h, ite_true]; rfl
  · simp only [h, ite_false]; rfl

/-- shape check from the shared numerator -/
def sN (c : ℕ) (x : Shape) (n : ℕ) : Bool :=
  if c = 0 then false else decide (∀ i k : Fin 3, (DEN : ℤ) * rayK c x i k ≤ (n : ℤ) * hiL c i k)

theorem thK_eq (c : ℕ) (x : Shape) : thK c x =
    (if isT c = true then thOK (rayT x) (savedT (hiS (Gk c))) else thOK (rayO x) (savedO (hiS (Gk c)))) := rfl
theorem thOK_eq (rx rh : Fin 3 → Fin 3 → ℤ) : thOK rx rh =
    decide (∀ i k : Fin 3, (DEN : ℤ) * rx i k ≤ (thNum rx rh : ℤ) * rh i k) := rfl
theorem shapeOK_c (c : ℕ) (x : Shape) :
    (if c = 0 then false else thK c x) = sN c x (thNum (rayK c x) (hiL c)) := by
  unfold sN
  by_cases h : c = 0
  · rw [if_pos h, if_pos h]
  · rw [if_neg h, if_neg h]
    rw [thK_eq, hiL_eq]
    by_cases h2 : isT c = true
    · rw [if_pos h2, thOK_eq]
      simp only [rayK, savedK, h2, ite_true]
    · rw [if_neg h2, thOK_eq]
      simp only [rayK, savedK, h2, Bool.false_eq_true, ite_false]

theorem shapeOK_eq (x : Shape) : shapeOK x = sN (cls x) x (thNum (rayK (cls x) x) (hiL (cls x))) :=
  shapeOK_c (cls x) x

def gtG (id t : ℕ) (p : ℕ × ℕ) (G : ℕ) : Bool :=
  let x : Shape := ⟨p.1, p.2, t⟩
  let k : Low6966Allocation.Band := ⟨id % 34, Nat.mod_lt _ (by decide)⟩
  let l := Low6966Allocation.order (Low6966Allocation.bandOrders k) x
  Nat.blt 0 l && Nat.ble (additiveBase x l + nonsharedFee x l + G)
    (Low6966Allocation.allowance k ((Low6966Allocation.start k).t + t) p.1 p.2 t)

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

theorem both_of_chunks (id t N : ℕ) (hN : (Low6966Gate.gateList id t).length ≤ 32 * N)
    (h : ∀ i, i < N → (chunkOf (Low6966Gate.gateList id t) i).all (fF id t) = true) :
    one id t = true ∧ gtOne id t = true := by
  have h1 : ∀ i, i < N → (chunkOf (Low6966Gate.gateList id t) i).all (oneF id t) = true := by
    intro i hi
    have := h i hi
    simp only [fF_eq, List.all_eq_true, Bool.and_eq_true] at this ⊢
    exact fun p hp => (this p hp).1
  have h2 : ∀ i, i < N → (chunkOf (Low6966Gate.gateList id t) i).all (gtF id t) = true := by
    intro i hi
    have := h i hi
    simp only [fF_eq, List.all_eq_true, Bool.and_eq_true] at this ⊢
    exact fun p hp => (this p hp).2
  exact ⟨one_of_chunks id t N hN h1, gtOne_of_chunks id t N hN h2⟩

end Gate6966Fin

end Merged_Witness6966Chunk

-- merged module G6966Check0
section Merged_G6966Check0
set_option Elab.async false
set_option maxRecDepth 200000
set_option maxHeartbeats 8000000
namespace Gate6966Fin
theorem f_0_2_0 : (chunkOf (Low6966Gate.gateList 0 2) 0).all (fF 0 2) = true := by decide +kernel
theorem f_0_2_1 : (chunkOf (Low6966Gate.gateList 0 2) 1).all (fF 0 2) = true := by decide +kernel
theorem f_0_2_2 : (chunkOf (Low6966Gate.gateList 0 2) 2).all (fF 0 2) = true := by decide +kernel
theorem f_0_2_3 : (chunkOf (Low6966Gate.gateList 0 2) 3).all (fF 0 2) = true := by decide +kernel
theorem f_0_2_4 : (chunkOf (Low6966Gate.gateList 0 2) 4).all (fF 0 2) = true := by decide +kernel
theorem f_0_2_5 : (chunkOf (Low6966Gate.gateList 0 2) 5).all (fF 0 2) = true := by decide +kernel
theorem f_0_2_6 : (chunkOf (Low6966Gate.gateList 0 2) 6).all (fF 0 2) = true := by decide +kernel
theorem f_0_2_7 : (chunkOf (Low6966Gate.gateList 0 2) 7).all (fF 0 2) = true := by decide +kernel
theorem f_0_2_8 : (chunkOf (Low6966Gate.gateList 0 2) 8).all (fF 0 2) = true := by decide +kernel
theorem f_0_2_9 : (chunkOf (Low6966Gate.gateList 0 2) 9).all (fF 0 2) = true := by decide +kernel
theorem f_0_2_10 : (chunkOf (Low6966Gate.gateList 0 2) 10).all (fF 0 2) = true := by decide +kernel
theorem fb_0_2 : one 0 2 = true ∧ gtOne 0 2 = true :=
  both_of_chunks 0 2 11 (by decide +kernel) (fun i hi => by
    interval_cases i
    · exact f_0_2_0
    · exact f_0_2_1
    · exact f_0_2_2
    · exact f_0_2_3
    · exact f_0_2_4
    · exact f_0_2_5
    · exact f_0_2_6
    · exact f_0_2_7
    · exact f_0_2_8
    · exact f_0_2_9
    · exact f_0_2_10
  )
theorem f_0_3_0 : (chunkOf (Low6966Gate.gateList 0 3) 0).all (fF 0 3) = true := by decide +kernel
theorem f_0_3_1 : (chunkOf (Low6966Gate.gateList 0 3) 1).all (fF 0 3) = true := by decide +kernel
theorem f_0_3_2 : (chunkOf (Low6966Gate.gateList 0 3) 2).all (fF 0 3) = true := by decide +kernel
theorem f_0_3_3 : (chunkOf (Low6966Gate.gateList 0 3) 3).all (fF 0 3) = true := by decide +kernel
theorem f_0_3_4 : (chunkOf (Low6966Gate.gateList 0 3) 4).all (fF 0 3) = true := by decide +kernel
theorem f_0_3_5 : (chunkOf (Low6966Gate.gateList 0 3) 5).all (fF 0 3) = true := by decide +kernel
theorem f_0_3_6 : (chunkOf (Low6966Gate.gateList 0 3) 6).all (fF 0 3) = true := by decide +kernel
theorem f_0_3_7 : (chunkOf (Low6966Gate.gateList 0 3) 7).all (fF 0 3) = true := by decide +kernel
theorem f_0_3_8 : (chunkOf (Low6966Gate.gateList 0 3) 8).all (fF 0 3) = true := by decide +kernel
theorem fb_0_3 : one 0 3 = true ∧ gtOne 0 3 = true :=
  both_of_chunks 0 3 9 (by decide +kernel) (fun i hi => by
    interval_cases i
    · exact f_0_3_0
    · exact f_0_3_1
    · exact f_0_3_2
    · exact f_0_3_3
    · exact f_0_3_4
    · exact f_0_3_5
    · exact f_0_3_6
    · exact f_0_3_7
    · exact f_0_3_8
  )
theorem f_0_4_0 : (chunkOf (Low6966Gate.gateList 0 4) 0).all (fF 0 4) = true := by decide +kernel
theorem f_0_4_1 : (chunkOf (Low6966Gate.gateList 0 4) 1).all (fF 0 4) = true := by decide +kernel
theorem f_0_4_2 : (chunkOf (Low6966Gate.gateList 0 4) 2).all (fF 0 4) = true := by decide +kernel
theorem f_0_4_3 : (chunkOf (Low6966Gate.gateList 0 4) 3).all (fF 0 4) = true := by decide +kernel
theorem f_0_4_4 : (chunkOf (Low6966Gate.gateList 0 4) 4).all (fF 0 4) = true := by decide +kernel
theorem f_0_4_5 : (chunkOf (Low6966Gate.gateList 0 4) 5).all (fF 0 4) = true := by decide +kernel
theorem f_0_4_6 : (chunkOf (Low6966Gate.gateList 0 4) 6).all (fF 0 4) = true := by decide +kernel
theorem f_0_4_7 : (chunkOf (Low6966Gate.gateList 0 4) 7).all (fF 0 4) = true := by decide +kernel
theorem f_0_4_8 : (chunkOf (Low6966Gate.gateList 0 4) 8).all (fF 0 4) = true := by decide +kernel
theorem f_0_4_9 : (chunkOf (Low6966Gate.gateList 0 4) 9).all (fF 0 4) = true := by decide +kernel
theorem f_0_4_10 : (chunkOf (Low6966Gate.gateList 0 4) 10).all (fF 0 4) = true := by decide +kernel
theorem fb_0_4 : one 0 4 = true ∧ gtOne 0 4 = true :=
  both_of_chunks 0 4 11 (by decide +kernel) (fun i hi => by
    interval_cases i
    · exact f_0_4_0
    · exact f_0_4_1
    · exact f_0_4_2
    · exact f_0_4_3
    · exact f_0_4_4
    · exact f_0_4_5
    · exact f_0_4_6
    · exact f_0_4_7
    · exact f_0_4_8
    · exact f_0_4_9
    · exact f_0_4_10
  )
theorem f_0_5_0 : (chunkOf (Low6966Gate.gateList 0 5) 0).all (fF 0 5) = true := by decide +kernel
theorem f_0_5_1 : (chunkOf (Low6966Gate.gateList 0 5) 1).all (fF 0 5) = true := by decide +kernel
theorem f_0_5_2 : (chunkOf (Low6966Gate.gateList 0 5) 2).all (fF 0 5) = true := by decide +kernel
theorem f_0_5_3 : (chunkOf (Low6966Gate.gateList 0 5) 3).all (fF 0 5) = true := by decide +kernel
theorem f_0_5_4 : (chunkOf (Low6966Gate.gateList 0 5) 4).all (fF 0 5) = true := by decide +kernel
theorem f_0_5_5 : (chunkOf (Low6966Gate.gateList 0 5) 5).all (fF 0 5) = true := by decide +kernel
theorem f_0_5_6 : (chunkOf (Low6966Gate.gateList 0 5) 6).all (fF 0 5) = true := by decide +kernel
theorem f_0_5_7 : (chunkOf (Low6966Gate.gateList 0 5) 7).all (fF 0 5) = true := by decide +kernel
theorem f_0_5_8 : (chunkOf (Low6966Gate.gateList 0 5) 8).all (fF 0 5) = true := by decide +kernel
theorem f_0_5_9 : (chunkOf (Low6966Gate.gateList 0 5) 9).all (fF 0 5) = true := by decide +kernel
theorem f_0_5_10 : (chunkOf (Low6966Gate.gateList 0 5) 10).all (fF 0 5) = true := by decide +kernel
theorem f_0_5_11 : (chunkOf (Low6966Gate.gateList 0 5) 11).all (fF 0 5) = true := by decide +kernel
theorem f_0_5_12 : (chunkOf (Low6966Gate.gateList 0 5) 12).all (fF 0 5) = true := by decide +kernel
theorem fb_0_5 : one 0 5 = true ∧ gtOne 0 5 = true :=
  both_of_chunks 0 5 13 (by decide +kernel) (fun i hi => by
    interval_cases i
    · exact f_0_5_0
    · exact f_0_5_1
    · exact f_0_5_2
    · exact f_0_5_3
    · exact f_0_5_4
    · exact f_0_5_5
    · exact f_0_5_6
    · exact f_0_5_7
    · exact f_0_5_8
    · exact f_0_5_9
    · exact f_0_5_10
    · exact f_0_5_11
    · exact f_0_5_12
  )
theorem f_0_6_0 : (chunkOf (Low6966Gate.gateList 0 6) 0).all (fF 0 6) = true := by decide +kernel
theorem f_0_6_1 : (chunkOf (Low6966Gate.gateList 0 6) 1).all (fF 0 6) = true := by decide +kernel
theorem f_0_6_2 : (chunkOf (Low6966Gate.gateList 0 6) 2).all (fF 0 6) = true := by decide +kernel
theorem f_0_6_3 : (chunkOf (Low6966Gate.gateList 0 6) 3).all (fF 0 6) = true := by decide +kernel
theorem f_0_6_4 : (chunkOf (Low6966Gate.gateList 0 6) 4).all (fF 0 6) = true := by decide +kernel
theorem f_0_6_5 : (chunkOf (Low6966Gate.gateList 0 6) 5).all (fF 0 6) = true := by decide +kernel
theorem f_0_6_6 : (chunkOf (Low6966Gate.gateList 0 6) 6).all (fF 0 6) = true := by decide +kernel
theorem f_0_6_7 : (chunkOf (Low6966Gate.gateList 0 6) 7).all (fF 0 6) = true := by decide +kernel
theorem f_0_6_8 : (chunkOf (Low6966Gate.gateList 0 6) 8).all (fF 0 6) = true := by decide +kernel
theorem f_0_6_9 : (chunkOf (Low6966Gate.gateList 0 6) 9).all (fF 0 6) = true := by decide +kernel
theorem f_0_6_10 : (chunkOf (Low6966Gate.gateList 0 6) 10).all (fF 0 6) = true := by decide +kernel
theorem f_0_6_11 : (chunkOf (Low6966Gate.gateList 0 6) 11).all (fF 0 6) = true := by decide +kernel
theorem f_0_6_12 : (chunkOf (Low6966Gate.gateList 0 6) 12).all (fF 0 6) = true := by decide +kernel
theorem f_0_6_13 : (chunkOf (Low6966Gate.gateList 0 6) 13).all (fF 0 6) = true := by decide +kernel
theorem f_0_6_14 : (chunkOf (Low6966Gate.gateList 0 6) 14).all (fF 0 6) = true := by decide +kernel
theorem f_0_6_15 : (chunkOf (Low6966Gate.gateList 0 6) 15).all (fF 0 6) = true := by decide +kernel
theorem fb_0_6 : one 0 6 = true ∧ gtOne 0 6 = true :=
  both_of_chunks 0 6 16 (by decide +kernel) (fun i hi => by
    interval_cases i
    · exact f_0_6_0
    · exact f_0_6_1
    · exact f_0_6_2
    · exact f_0_6_3
    · exact f_0_6_4
    · exact f_0_6_5
    · exact f_0_6_6
    · exact f_0_6_7
    · exact f_0_6_8
    · exact f_0_6_9
    · exact f_0_6_10
    · exact f_0_6_11
    · exact f_0_6_12
    · exact f_0_6_13
    · exact f_0_6_14
    · exact f_0_6_15
  )
theorem f_0_7_0 : (chunkOf (Low6966Gate.gateList 0 7) 0).all (fF 0 7) = true := by decide +kernel
theorem f_0_7_1 : (chunkOf (Low6966Gate.gateList 0 7) 1).all (fF 0 7) = true := by decide +kernel
theorem f_0_7_2 : (chunkOf (Low6966Gate.gateList 0 7) 2).all (fF 0 7) = true := by decide +kernel
theorem f_0_7_3 : (chunkOf (Low6966Gate.gateList 0 7) 3).all (fF 0 7) = true := by decide +kernel
theorem f_0_7_4 : (chunkOf (Low6966Gate.gateList 0 7) 4).all (fF 0 7) = true := by decide +kernel
theorem f_0_7_5 : (chunkOf (Low6966Gate.gateList 0 7) 5).all (fF 0 7) = true := by decide +kernel
theorem f_0_7_6 : (chunkOf (Low6966Gate.gateList 0 7) 6).all (fF 0 7) = true := by decide +kernel
theorem f_0_7_7 : (chunkOf (Low6966Gate.gateList 0 7) 7).all (fF 0 7) = true := by decide +kernel
theorem f_0_7_8 : (chunkOf (Low6966Gate.gateList 0 7) 8).all (fF 0 7) = true := by decide +kernel
theorem f_0_7_9 : (chunkOf (Low6966Gate.gateList 0 7) 9).all (fF 0 7) = true := by decide +kernel
theorem f_0_7_10 : (chunkOf (Low6966Gate.gateList 0 7) 10).all (fF 0 7) = true := by decide +kernel
theorem f_0_7_11 : (chunkOf (Low6966Gate.gateList 0 7) 11).all (fF 0 7) = true := by decide +kernel
theorem f_0_7_12 : (chunkOf (Low6966Gate.gateList 0 7) 12).all (fF 0 7) = true := by decide +kernel
theorem f_0_7_13 : (chunkOf (Low6966Gate.gateList 0 7) 13).all (fF 0 7) = true := by decide +kernel
theorem f_0_7_14 : (chunkOf (Low6966Gate.gateList 0 7) 14).all (fF 0 7) = true := by decide +kernel
theorem f_0_7_15 : (chunkOf (Low6966Gate.gateList 0 7) 15).all (fF 0 7) = true := by decide +kernel
theorem f_0_7_16 : (chunkOf (Low6966Gate.gateList 0 7) 16).all (fF 0 7) = true := by decide +kernel
theorem fb_0_7 : one 0 7 = true ∧ gtOne 0 7 = true :=
  both_of_chunks 0 7 17 (by decide +kernel) (fun i hi => by
    interval_cases i
    · exact f_0_7_0
    · exact f_0_7_1
    · exact f_0_7_2
    · exact f_0_7_3
    · exact f_0_7_4
    · exact f_0_7_5
    · exact f_0_7_6
    · exact f_0_7_7
    · exact f_0_7_8
    · exact f_0_7_9
    · exact f_0_7_10
    · exact f_0_7_11
    · exact f_0_7_12
    · exact f_0_7_13
    · exact f_0_7_14
    · exact f_0_7_15
    · exact f_0_7_16
  )
theorem f_0_8_0 : (chunkOf (Low6966Gate.gateList 0 8) 0).all (fF 0 8) = true := by decide +kernel
theorem f_0_8_1 : (chunkOf (Low6966Gate.gateList 0 8) 1).all (fF 0 8) = true := by decide +kernel
theorem f_0_8_2 : (chunkOf (Low6966Gate.gateList 0 8) 2).all (fF 0 8) = true := by decide +kernel
theorem f_0_8_3 : (chunkOf (Low6966Gate.gateList 0 8) 3).all (fF 0 8) = true := by decide +kernel
theorem f_0_8_4 : (chunkOf (Low6966Gate.gateList 0 8) 4).all (fF 0 8) = true := by decide +kernel
theorem f_0_8_5 : (chunkOf (Low6966Gate.gateList 0 8) 5).all (fF 0 8) = true := by decide +kernel
theorem f_0_8_6 : (chunkOf (Low6966Gate.gateList 0 8) 6).all (fF 0 8) = true := by decide +kernel
theorem f_0_8_7 : (chunkOf (Low6966Gate.gateList 0 8) 7).all (fF 0 8) = true := by decide +kernel
theorem f_0_8_8 : (chunkOf (Low6966Gate.gateList 0 8) 8).all (fF 0 8) = true := by decide +kernel
theorem f_0_8_9 : (chunkOf (Low6966Gate.gateList 0 8) 9).all (fF 0 8) = true := by decide +kernel
theorem f_0_8_10 : (chunkOf (Low6966Gate.gateList 0 8) 10).all (fF 0 8) = true := by decide +kernel
theorem f_0_8_11 : (chunkOf (Low6966Gate.gateList 0 8) 11).all (fF 0 8) = true := by decide +kernel
theorem f_0_8_12 : (chunkOf (Low6966Gate.gateList 0 8) 12).all (fF 0 8) = true := by decide +kernel
theorem f_0_8_13 : (chunkOf (Low6966Gate.gateList 0 8) 13).all (fF 0 8) = true := by decide +kernel
theorem f_0_8_14 : (chunkOf (Low6966Gate.gateList 0 8) 14).all (fF 0 8) = true := by decide +kernel
theorem f_0_8_15 : (chunkOf (Low6966Gate.gateList 0 8) 15).all (fF 0 8) = true := by decide +kernel
theorem f_0_8_16 : (chunkOf (Low6966Gate.gateList 0 8) 16).all (fF 0 8) = true := by decide +kernel
theorem f_0_8_17 : (chunkOf (Low6966Gate.gateList 0 8) 17).all (fF 0 8) = true := by decide +kernel
theorem f_0_8_18 : (chunkOf (Low6966Gate.gateList 0 8) 18).all (fF 0 8) = true := by decide +kernel
theorem fb_0_8 : one 0 8 = true ∧ gtOne 0 8 = true :=
  both_of_chunks 0 8 19 (by decide +kernel) (fun i hi => by
    interval_cases i
    · exact f_0_8_0
    · exact f_0_8_1
    · exact f_0_8_2
    · exact f_0_8_3
    · exact f_0_8_4
    · exact f_0_8_5
    · exact f_0_8_6
    · exact f_0_8_7
    · exact f_0_8_8
    · exact f_0_8_9
    · exact f_0_8_10
    · exact f_0_8_11
    · exact f_0_8_12
    · exact f_0_8_13
    · exact f_0_8_14
    · exact f_0_8_15
    · exact f_0_8_16
    · exact f_0_8_17
    · exact f_0_8_18
  )
theorem f_0_9_0 : (chunkOf (Low6966Gate.gateList 0 9) 0).all (fF 0 9) = true := by decide +kernel
theorem f_0_9_1 : (chunkOf (Low6966Gate.gateList 0 9) 1).all (fF 0 9) = true := by decide +kernel
theorem f_0_9_2 : (chunkOf (Low6966Gate.gateList 0 9) 2).all (fF 0 9) = true := by decide +kernel
theorem f_0_9_3 : (chunkOf (Low6966Gate.gateList 0 9) 3).all (fF 0 9) = true := by decide +kernel
theorem f_0_9_4 : (chunkOf (Low6966Gate.gateList 0 9) 4).all (fF 0 9) = true := by decide +kernel
theorem f_0_9_5 : (chunkOf (Low6966Gate.gateList 0 9) 5).all (fF 0 9) = true := by decide +kernel
theorem f_0_9_6 : (chunkOf (Low6966Gate.gateList 0 9) 6).all (fF 0 9) = true := by decide +kernel
theorem f_0_9_7 : (chunkOf (Low6966Gate.gateList 0 9) 7).all (fF 0 9) = true := by decide +kernel
theorem f_0_9_8 : (chunkOf (Low6966Gate.gateList 0 9) 8).all (fF 0 9) = true := by decide +kernel
theorem f_0_9_9 : (chunkOf (Low6966Gate.gateList 0 9) 9).all (fF 0 9) = true := by decide +kernel
theorem f_0_9_10 : (chunkOf (Low6966Gate.gateList 0 9) 10).all (fF 0 9) = true := by decide +kernel
theorem f_0_9_11 : (chunkOf (Low6966Gate.gateList 0 9) 11).all (fF 0 9) = true := by decide +kernel
theorem f_0_9_12 : (chunkOf (Low6966Gate.gateList 0 9) 12).all (fF 0 9) = true := by decide +kernel
theorem f_0_9_13 : (chunkOf (Low6966Gate.gateList 0 9) 13).all (fF 0 9) = true := by decide +kernel
theorem f_0_9_14 : (chunkOf (Low6966Gate.gateList 0 9) 14).all (fF 0 9) = true := by decide +kernel
theorem f_0_9_15 : (chunkOf (Low6966Gate.gateList 0 9) 15).all (fF 0 9) = true := by decide +kernel
theorem f_0_9_16 : (chunkOf (Low6966Gate.gateList 0 9) 16).all (fF 0 9) = true := by decide +kernel
theorem f_0_9_17 : (chunkOf (Low6966Gate.gateList 0 9) 17).all (fF 0 9) = true := by decide +kernel
theorem f_0_9_18 : (chunkOf (Low6966Gate.gateList 0 9) 18).all (fF 0 9) = true := by decide +kernel
theorem f_0_9_19 : (chunkOf (Low6966Gate.gateList 0 9) 19).all (fF 0 9) = true := by decide +kernel
theorem fb_0_9 : one 0 9 = true ∧ gtOne 0 9 = true :=
  both_of_chunks 0 9 20 (by decide +kernel) (fun i hi => by
    interval_cases i
    · exact f_0_9_0
    · exact f_0_9_1
    · exact f_0_9_2
    · exact f_0_9_3
    · exact f_0_9_4
    · exact f_0_9_5
    · exact f_0_9_6
    · exact f_0_9_7
    · exact f_0_9_8
    · exact f_0_9_9
    · exact f_0_9_10
    · exact f_0_9_11
    · exact f_0_9_12
    · exact f_0_9_13
    · exact f_0_9_14
    · exact f_0_9_15
    · exact f_0_9_16
    · exact f_0_9_17
    · exact f_0_9_18
    · exact f_0_9_19
  )
theorem f_0_10_0 : (chunkOf (Low6966Gate.gateList 0 10) 0).all (fF 0 10) = true := by decide +kernel
theorem f_0_10_1 : (chunkOf (Low6966Gate.gateList 0 10) 1).all (fF 0 10) = true := by decide +kernel
theorem f_0_10_2 : (chunkOf (Low6966Gate.gateList 0 10) 2).all (fF 0 10) = true := by decide +kernel
theorem f_0_10_3 : (chunkOf (Low6966Gate.gateList 0 10) 3).all (fF 0 10) = true := by decide +kernel
theorem f_0_10_4 : (chunkOf (Low6966Gate.gateList 0 10) 4).all (fF 0 10) = true := by decide +kernel
theorem f_0_10_5 : (chunkOf (Low6966Gate.gateList 0 10) 5).all (fF 0 10) = true := by decide +kernel
theorem f_0_10_6 : (chunkOf (Low6966Gate.gateList 0 10) 6).all (fF 0 10) = true := by decide +kernel
theorem f_0_10_7 : (chunkOf (Low6966Gate.gateList 0 10) 7).all (fF 0 10) = true := by decide +kernel
theorem f_0_10_8 : (chunkOf (Low6966Gate.gateList 0 10) 8).all (fF 0 10) = true := by decide +kernel
theorem f_0_10_9 : (chunkOf (Low6966Gate.gateList 0 10) 9).all (fF 0 10) = true := by decide +kernel
theorem f_0_10_10 : (chunkOf (Low6966Gate.gateList 0 10) 10).all (fF 0 10) = true := by decide +kernel
theorem f_0_10_11 : (chunkOf (Low6966Gate.gateList 0 10) 11).all (fF 0 10) = true := by decide +kernel
theorem f_0_10_12 : (chunkOf (Low6966Gate.gateList 0 10) 12).all (fF 0 10) = true := by decide +kernel
theorem f_0_10_13 : (chunkOf (Low6966Gate.gateList 0 10) 13).all (fF 0 10) = true := by decide +kernel
theorem f_0_10_14 : (chunkOf (Low6966Gate.gateList 0 10) 14).all (fF 0 10) = true := by decide +kernel
theorem f_0_10_15 : (chunkOf (Low6966Gate.gateList 0 10) 15).all (fF 0 10) = true := by decide +kernel
theorem f_0_10_16 : (chunkOf (Low6966Gate.gateList 0 10) 16).all (fF 0 10) = true := by decide +kernel
theorem f_0_10_17 : (chunkOf (Low6966Gate.gateList 0 10) 17).all (fF 0 10) = true := by decide +kernel
theorem f_0_10_18 : (chunkOf (Low6966Gate.gateList 0 10) 18).all (fF 0 10) = true := by decide +kernel
theorem f_0_10_19 : (chunkOf (Low6966Gate.gateList 0 10) 19).all (fF 0 10) = true := by decide +kernel
theorem f_0_10_20 : (chunkOf (Low6966Gate.gateList 0 10) 20).all (fF 0 10) = true := by decide +kernel
theorem fb_0_10 : one 0 10 = true ∧ gtOne 0 10 = true :=
  both_of_chunks 0 10 21 (by decide +kernel) (fun i hi => by
    interval_cases i
    · exact f_0_10_0
    · exact f_0_10_1
    · exact f_0_10_2
    · exact f_0_10_3
    · exact f_0_10_4
    · exact f_0_10_5
    · exact f_0_10_6
    · exact f_0_10_7
    · exact f_0_10_8
    · exact f_0_10_9
    · exact f_0_10_10
    · exact f_0_10_11
    · exact f_0_10_12
    · exact f_0_10_13
    · exact f_0_10_14
    · exact f_0_10_15
    · exact f_0_10_16
    · exact f_0_10_17
    · exact f_0_10_18
    · exact f_0_10_19
    · exact f_0_10_20
  )
theorem f_0_11_0 : (chunkOf (Low6966Gate.gateList 0 11) 0).all (fF 0 11) = true := by decide +kernel
theorem f_0_11_1 : (chunkOf (Low6966Gate.gateList 0 11) 1).all (fF 0 11) = true := by decide +kernel
theorem f_0_11_2 : (chunkOf (Low6966Gate.gateList 0 11) 2).all (fF 0 11) = true := by decide +kernel
theorem f_0_11_3 : (chunkOf (Low6966Gate.gateList 0 11) 3).all (fF 0 11) = true := by decide +kernel
theorem f_0_11_4 : (chunkOf (Low6966Gate.gateList 0 11) 4).all (fF 0 11) = true := by decide +kernel
theorem f_0_11_5 : (chunkOf (Low6966Gate.gateList 0 11) 5).all (fF 0 11) = true := by decide +kernel
theorem f_0_11_6 : (chunkOf (Low6966Gate.gateList 0 11) 6).all (fF 0 11) = true := by decide +kernel
theorem f_0_11_7 : (chunkOf (Low6966Gate.gateList 0 11) 7).all (fF 0 11) = true := by decide +kernel
theorem f_0_11_8 : (chunkOf (Low6966Gate.gateList 0 11) 8).all (fF 0 11) = true := by decide +kernel
theorem f_0_11_9 : (chunkOf (Low6966Gate.gateList 0 11) 9).all (fF 0 11) = true := by decide +kernel
theorem f_0_11_10 : (chunkOf (Low6966Gate.gateList 0 11) 10).all (fF 0 11) = true := by decide +kernel
theorem f_0_11_11 : (chunkOf (Low6966Gate.gateList 0 11) 11).all (fF 0 11) = true := by decide +kernel
theorem f_0_11_12 : (chunkOf (Low6966Gate.gateList 0 11) 12).all (fF 0 11) = true := by decide +kernel
theorem f_0_11_13 : (chunkOf (Low6966Gate.gateList 0 11) 13).all (fF 0 11) = true := by decide +kernel
theorem f_0_11_14 : (chunkOf (Low6966Gate.gateList 0 11) 14).all (fF 0 11) = true := by decide +kernel
theorem f_0_11_15 : (chunkOf (Low6966Gate.gateList 0 11) 15).all (fF 0 11) = true := by decide +kernel
theorem f_0_11_16 : (chunkOf (Low6966Gate.gateList 0 11) 16).all (fF 0 11) = true := by decide +kernel
theorem f_0_11_17 : (chunkOf (Low6966Gate.gateList 0 11) 17).all (fF 0 11) = true := by decide +kernel
theorem f_0_11_18 : (chunkOf (Low6966Gate.gateList 0 11) 18).all (fF 0 11) = true := by decide +kernel
theorem f_0_11_19 : (chunkOf (Low6966Gate.gateList 0 11) 19).all (fF 0 11) = true := by decide +kernel
theorem f_0_11_20 : (chunkOf (Low6966Gate.gateList 0 11) 20).all (fF 0 11) = true := by decide +kernel
theorem f_0_11_21 : (chunkOf (Low6966Gate.gateList 0 11) 21).all (fF 0 11) = true := by decide +kernel
theorem fb_0_11 : one 0 11 = true ∧ gtOne 0 11 = true :=
  both_of_chunks 0 11 22 (by decide +kernel) (fun i hi => by
    interval_cases i
    · exact f_0_11_0
    · exact f_0_11_1
    · exact f_0_11_2
    · exact f_0_11_3
    · exact f_0_11_4
    · exact f_0_11_5
    · exact f_0_11_6
    · exact f_0_11_7
    · exact f_0_11_8
    · exact f_0_11_9
    · exact f_0_11_10
    · exact f_0_11_11
    · exact f_0_11_12
    · exact f_0_11_13
    · exact f_0_11_14
    · exact f_0_11_15
    · exact f_0_11_16
    · exact f_0_11_17
    · exact f_0_11_18
    · exact f_0_11_19
    · exact f_0_11_20
    · exact f_0_11_21
  )
theorem f_0_12_0 : (chunkOf (Low6966Gate.gateList 0 12) 0).all (fF 0 12) = true := by decide +kernel
theorem f_0_12_1 : (chunkOf (Low6966Gate.gateList 0 12) 1).all (fF 0 12) = true := by decide +kernel
theorem f_0_12_2 : (chunkOf (Low6966Gate.gateList 0 12) 2).all (fF 0 12) = true := by decide +kernel
theorem f_0_12_3 : (chunkOf (Low6966Gate.gateList 0 12) 3).all (fF 0 12) = true := by decide +kernel
theorem f_0_12_4 : (chunkOf (Low6966Gate.gateList 0 12) 4).all (fF 0 12) = true := by decide +kernel
theorem f_0_12_5 : (chunkOf (Low6966Gate.gateList 0 12) 5).all (fF 0 12) = true := by decide +kernel
theorem f_0_12_6 : (chunkOf (Low6966Gate.gateList 0 12) 6).all (fF 0 12) = true := by decide +kernel
theorem f_0_12_7 : (chunkOf (Low6966Gate.gateList 0 12) 7).all (fF 0 12) = true := by decide +kernel
theorem f_0_12_8 : (chunkOf (Low6966Gate.gateList 0 12) 8).all (fF 0 12) = true := by decide +kernel
theorem f_0_12_9 : (chunkOf (Low6966Gate.gateList 0 12) 9).all (fF 0 12) = true := by decide +kernel
theorem f_0_12_10 : (chunkOf (Low6966Gate.gateList 0 12) 10).all (fF 0 12) = true := by decide +kernel
theorem f_0_12_11 : (chunkOf (Low6966Gate.gateList 0 12) 11).all (fF 0 12) = true := by decide +kernel
theorem f_0_12_12 : (chunkOf (Low6966Gate.gateList 0 12) 12).all (fF 0 12) = true := by decide +kernel
theorem f_0_12_13 : (chunkOf (Low6966Gate.gateList 0 12) 13).all (fF 0 12) = true := by decide +kernel
theorem f_0_12_14 : (chunkOf (Low6966Gate.gateList 0 12) 14).all (fF 0 12) = true := by decide +kernel
theorem f_0_12_15 : (chunkOf (Low6966Gate.gateList 0 12) 15).all (fF 0 12) = true := by decide +kernel
theorem f_0_12_16 : (chunkOf (Low6966Gate.gateList 0 12) 16).all (fF 0 12) = true := by decide +kernel
theorem f_0_12_17 : (chunkOf (Low6966Gate.gateList 0 12) 17).all (fF 0 12) = true := by decide +kernel
theorem f_0_12_18 : (chunkOf (Low6966Gate.gateList 0 12) 18).all (fF 0 12) = true := by decide +kernel
theorem f_0_12_19 : (chunkOf (Low6966Gate.gateList 0 12) 19).all (fF 0 12) = true := by decide +kernel
theorem f_0_12_20 : (chunkOf (Low6966Gate.gateList 0 12) 20).all (fF 0 12) = true := by decide +kernel
theorem f_0_12_21 : (chunkOf (Low6966Gate.gateList 0 12) 21).all (fF 0 12) = true := by decide +kernel
theorem fb_0_12 : one 0 12 = true ∧ gtOne 0 12 = true :=
  both_of_chunks 0 12 22 (by decide +kernel) (fun i hi => by
    interval_cases i
    · exact f_0_12_0
    · exact f_0_12_1
    · exact f_0_12_2
    · exact f_0_12_3
    · exact f_0_12_4
    · exact f_0_12_5
    · exact f_0_12_6
    · exact f_0_12_7
    · exact f_0_12_8
    · exact f_0_12_9
    · exact f_0_12_10
    · exact f_0_12_11
    · exact f_0_12_12
    · exact f_0_12_13
    · exact f_0_12_14
    · exact f_0_12_15
    · exact f_0_12_16
    · exact f_0_12_17
    · exact f_0_12_18
    · exact f_0_12_19
    · exact f_0_12_20
    · exact f_0_12_21
  )
theorem f_0_13_0 : (chunkOf (Low6966Gate.gateList 0 13) 0).all (fF 0 13) = true := by decide +kernel
theorem f_0_13_1 : (chunkOf (Low6966Gate.gateList 0 13) 1).all (fF 0 13) = true := by decide +kernel
theorem f_0_13_2 : (chunkOf (Low6966Gate.gateList 0 13) 2).all (fF 0 13) = true := by decide +kernel
theorem f_0_13_3 : (chunkOf (Low6966Gate.gateList 0 13) 3).all (fF 0 13) = true := by decide +kernel
theorem f_0_13_4 : (chunkOf (Low6966Gate.gateList 0 13) 4).all (fF 0 13) = true := by decide +kernel
theorem f_0_13_5 : (chunkOf (Low6966Gate.gateList 0 13) 5).all (fF 0 13) = true := by decide +kernel
theorem f_0_13_6 : (chunkOf (Low6966Gate.gateList 0 13) 6).all (fF 0 13) = true := by decide +kernel
theorem f_0_13_7 : (chunkOf (Low6966Gate.gateList 0 13) 7).all (fF 0 13) = true := by decide +kernel
theorem f_0_13_8 : (chunkOf (Low6966Gate.gateList 0 13) 8).all (fF 0 13) = true := by decide +kernel
theorem f_0_13_9 : (chunkOf (Low6966Gate.gateList 0 13) 9).all (fF 0 13) = true := by decide +kernel
theorem f_0_13_10 : (chunkOf (Low6966Gate.gateList 0 13) 10).all (fF 0 13) = true := by decide +kernel
theorem f_0_13_11 : (chunkOf (Low6966Gate.gateList 0 13) 11).all (fF 0 13) = true := by decide +kernel
theorem f_0_13_12 : (chunkOf (Low6966Gate.gateList 0 13) 12).all (fF 0 13) = true := by decide +kernel
theorem f_0_13_13 : (chunkOf (Low6966Gate.gateList 0 13) 13).all (fF 0 13) = true := by decide +kernel
theorem f_0_13_14 : (chunkOf (Low6966Gate.gateList 0 13) 14).all (fF 0 13) = true := by decide +kernel
theorem f_0_13_15 : (chunkOf (Low6966Gate.gateList 0 13) 15).all (fF 0 13) = true := by decide +kernel
theorem f_0_13_16 : (chunkOf (Low6966Gate.gateList 0 13) 16).all (fF 0 13) = true := by decide +kernel
theorem f_0_13_17 : (chunkOf (Low6966Gate.gateList 0 13) 17).all (fF 0 13) = true := by decide +kernel
theorem f_0_13_18 : (chunkOf (Low6966Gate.gateList 0 13) 18).all (fF 0 13) = true := by decide +kernel
theorem f_0_13_19 : (chunkOf (Low6966Gate.gateList 0 13) 19).all (fF 0 13) = true := by decide +kernel
theorem f_0_13_20 : (chunkOf (Low6966Gate.gateList 0 13) 20).all (fF 0 13) = true := by decide +kernel
theorem f_0_13_21 : (chunkOf (Low6966Gate.gateList 0 13) 21).all (fF 0 13) = true := by decide +kernel
theorem f_0_13_22 : (chunkOf (Low6966Gate.gateList 0 13) 22).all (fF 0 13) = true := by decide +kernel
theorem f_0_13_23 : (chunkOf (Low6966Gate.gateList 0 13) 23).all (fF 0 13) = true := by decide +kernel
theorem fb_0_13 : one 0 13 = true ∧ gtOne 0 13 = true :=
  both_of_chunks 0 13 24 (by decide +kernel) (fun i hi => by
    interval_cases i
    · exact f_0_13_0
    · exact f_0_13_1
    · exact f_0_13_2
    · exact f_0_13_3
    · exact f_0_13_4
    · exact f_0_13_5
    · exact f_0_13_6
    · exact f_0_13_7
    · exact f_0_13_8
    · exact f_0_13_9
    · exact f_0_13_10
    · exact f_0_13_11
    · exact f_0_13_12
    · exact f_0_13_13
    · exact f_0_13_14
    · exact f_0_13_15
    · exact f_0_13_16
    · exact f_0_13_17
    · exact f_0_13_18
    · exact f_0_13_19
    · exact f_0_13_20
    · exact f_0_13_21
    · exact f_0_13_22
    · exact f_0_13_23
  )
theorem f_0_14_0 : (chunkOf (Low6966Gate.gateList 0 14) 0).all (fF 0 14) = true := by decide +kernel
theorem f_0_14_1 : (chunkOf (Low6966Gate.gateList 0 14) 1).all (fF 0 14) = true := by decide +kernel
theorem f_0_14_2 : (chunkOf (Low6966Gate.gateList 0 14) 2).all (fF 0 14) = true := by decide +kernel
theorem f_0_14_3 : (chunkOf (Low6966Gate.gateList 0 14) 3).all (fF 0 14) = true := by decide +kernel
theorem f_0_14_4 : (chunkOf (Low6966Gate.gateList 0 14) 4).all (fF 0 14) = true := by decide +kernel
theorem f_0_14_5 : (chunkOf (Low6966Gate.gateList 0 14) 5).all (fF 0 14) = true := by decide +kernel
theorem f_0_14_6 : (chunkOf (Low6966Gate.gateList 0 14) 6).all (fF 0 14) = true := by decide +kernel
theorem f_0_14_7 : (chunkOf (Low6966Gate.gateList 0 14) 7).all (fF 0 14) = true := by decide +kernel
theorem f_0_14_8 : (chunkOf (Low6966Gate.gateList 0 14) 8).all (fF 0 14) = true := by decide +kernel
theorem f_0_14_9 : (chunkOf (Low6966Gate.gateList 0 14) 9).all (fF 0 14) = true := by decide +kernel
theorem f_0_14_10 : (chunkOf (Low6966Gate.gateList 0 14) 10).all (fF 0 14) = true := by decide +kernel
theorem f_0_14_11 : (chunkOf (Low6966Gate.gateList 0 14) 11).all (fF 0 14) = true := by decide +kernel
theorem f_0_14_12 : (chunkOf (Low6966Gate.gateList 0 14) 12).all (fF 0 14) = true := by decide +kernel
theorem f_0_14_13 : (chunkOf (Low6966Gate.gateList 0 14) 13).all (fF 0 14) = true := by decide +kernel
theorem f_0_14_14 : (chunkOf (Low6966Gate.gateList 0 14) 14).all (fF 0 14) = true := by decide +kernel
theorem f_0_14_15 : (chunkOf (Low6966Gate.gateList 0 14) 15).all (fF 0 14) = true := by decide +kernel
theorem f_0_14_16 : (chunkOf (Low6966Gate.gateList 0 14) 16).all (fF 0 14) = true := by decide +kernel
theorem f_0_14_17 : (chunkOf (Low6966Gate.gateList 0 14) 17).all (fF 0 14) = true := by decide +kernel
theorem f_0_14_18 : (chunkOf (Low6966Gate.gateList 0 14) 18).all (fF 0 14) = true := by decide +kernel
theorem f_0_14_19 : (chunkOf (Low6966Gate.gateList 0 14) 19).all (fF 0 14) = true := by decide +kernel
theorem f_0_14_20 : (chunkOf (Low6966Gate.gateList 0 14) 20).all (fF 0 14) = true := by decide +kernel
theorem f_0_14_21 : (chunkOf (Low6966Gate.gateList 0 14) 21).all (fF 0 14) = true := by decide +kernel
theorem f_0_14_22 : (chunkOf (Low6966Gate.gateList 0 14) 22).all (fF 0 14) = true := by decide +kernel
theorem f_0_14_23 : (chunkOf (Low6966Gate.gateList 0 14) 23).all (fF 0 14) = true := by decide +kernel
theorem f_0_14_24 : (chunkOf (Low6966Gate.gateList 0 14) 24).all (fF 0 14) = true := by decide +kernel
theorem f_0_14_25 : (chunkOf (Low6966Gate.gateList 0 14) 25).all (fF 0 14) = true := by decide +kernel
theorem fb_0_14 : one 0 14 = true ∧ gtOne 0 14 = true :=
  both_of_chunks 0 14 26 (by decide +kernel) (fun i hi => by
    interval_cases i
    · exact f_0_14_0
    · exact f_0_14_1
    · exact f_0_14_2
    · exact f_0_14_3
    · exact f_0_14_4
    · exact f_0_14_5
    · exact f_0_14_6
    · exact f_0_14_7
    · exact f_0_14_8
    · exact f_0_14_9
    · exact f_0_14_10
    · exact f_0_14_11
    · exact f_0_14_12
    · exact f_0_14_13
    · exact f_0_14_14
    · exact f_0_14_15
    · exact f_0_14_16
    · exact f_0_14_17
    · exact f_0_14_18
    · exact f_0_14_19
    · exact f_0_14_20
    · exact f_0_14_21
    · exact f_0_14_22
    · exact f_0_14_23
    · exact f_0_14_24
    · exact f_0_14_25
  )
theorem f_0_15_0 : (chunkOf (Low6966Gate.gateList 0 15) 0).all (fF 0 15) = true := by decide +kernel
theorem f_0_15_1 : (chunkOf (Low6966Gate.gateList 0 15) 1).all (fF 0 15) = true := by decide +kernel
theorem f_0_15_2 : (chunkOf (Low6966Gate.gateList 0 15) 2).all (fF 0 15) = true := by decide +kernel
theorem f_0_15_3 : (chunkOf (Low6966Gate.gateList 0 15) 3).all (fF 0 15) = true := by decide +kernel
theorem f_0_15_4 : (chunkOf (Low6966Gate.gateList 0 15) 4).all (fF 0 15) = true := by decide +kernel
theorem f_0_15_5 : (chunkOf (Low6966Gate.gateList 0 15) 5).all (fF 0 15) = true := by decide +kernel
theorem f_0_15_6 : (chunkOf (Low6966Gate.gateList 0 15) 6).all (fF 0 15) = true := by decide +kernel
theorem f_0_15_7 : (chunkOf (Low6966Gate.gateList 0 15) 7).all (fF 0 15) = true := by decide +kernel
theorem f_0_15_8 : (chunkOf (Low6966Gate.gateList 0 15) 8).all (fF 0 15) = true := by decide +kernel
theorem f_0_15_9 : (chunkOf (Low6966Gate.gateList 0 15) 9).all (fF 0 15) = true := by decide +kernel
theorem f_0_15_10 : (chunkOf (Low6966Gate.gateList 0 15) 10).all (fF 0 15) = true := by decide +kernel
theorem f_0_15_11 : (chunkOf (Low6966Gate.gateList 0 15) 11).all (fF 0 15) = true := by decide +kernel
theorem f_0_15_12 : (chunkOf (Low6966Gate.gateList 0 15) 12).all (fF 0 15) = true := by decide +kernel
theorem fb_0_15 : one 0 15 = true ∧ gtOne 0 15 = true :=
  both_of_chunks 0 15 13 (by decide +kernel) (fun i hi => by
    interval_cases i
    · exact f_0_15_0
    · exact f_0_15_1
    · exact f_0_15_2
    · exact f_0_15_3
    · exact f_0_15_4
    · exact f_0_15_5
    · exact f_0_15_6
    · exact f_0_15_7
    · exact f_0_15_8
    · exact f_0_15_9
    · exact f_0_15_10
    · exact f_0_15_11
    · exact f_0_15_12
  )
end Gate6966Fin

end Merged_G6966Check0
