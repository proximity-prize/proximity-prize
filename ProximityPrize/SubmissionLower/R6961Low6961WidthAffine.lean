import ProximityPrize.SubmissionLower.R6961Low6961SurfaceLinearFive

set_option Elab.async false
set_option maxHeartbeats 1800000
namespace Low6961WidthAffine
open K1_13 (Shape)
open Low6961Prices (BentCap addBent bentIntegral ambientMix tiltedSurface tiltedFits
  bentGraph bentLift taylorLength)
open Final50SharedPrice (signedFive signed_five_nonneg)

private abbrev Slot := BentCap × ℕ
private def atWidth (x : ℕ) (s : Slot) : BentCap :=
  (⟨s.1.1.b+x*s.2,s.1.1.j,s.1.1.t⟩,s.1.2)
private def add (a b : Slot) : Slot := (addBent a.1 b.1,a.2+b.2)
private def zero : Slot := ((⟨0,0,0⟩,0),0)

private theorem at_add (x : ℕ) (a b : Slot) :
    atWidth x (add a b) = addBent (atWidth x a) (atWidth x b) := by
  simp only [atWidth,add,addBent,Shape.plus,Prod.mk.injEq,Shape.mk.injEq,and_true]
  ring

private theorem fold_slots (x : ℕ) (s : List Slot) :
    (s.map (atWidth x)).foldl addBent (⟨0,0,0⟩,0) = atWidth x (s.foldl add zero) := by
  change (s.map (atWidth x)).foldl addBent (atWidth x zero) = _
  rw [List.foldl_map]
  exact List.foldl_hom (atWidth x) (fun a b => (at_add x a b).symm)

private def raw (s : List BentCap) : ℤ :=
  s.sublists.foldl (fun acc boxes =>
    let p := boxes.foldl addBent (⟨0,0,0⟩,0)
    acc + (-1 : ℤ) ^ (5-boxes.length) * bentIntegral p.1.b p.1.j p.1.t p.2) 0

private theorem integral_affine (B x W J T H : ℤ) :
    bentIntegral (B+x*W) J T H = bentIntegral B J T H + x *
      (bentIntegral (B+W) J T H-bentIntegral B J T H) := by
  simp only [bentIntegral]
  ring

private def integralTerm (boxes : List Slot) (x : ℕ) : ℤ :=
  let p := atWidth x (boxes.foldl add zero)
  (-1 : ℤ) ^ (5-boxes.length) * bentIntegral p.1.b p.1.j p.1.t p.2

private theorem term_affine (boxes : List Slot) (x : ℕ) :
    integralTerm boxes x = integralTerm boxes 0 + (x : ℤ) *
      (integralTerm boxes 1-integralTerm boxes 0) := by
  simp only [integralTerm, atWidth, Nat.cast_add, Nat.cast_mul, zero_mul, one_mul, add_zero, integral_affine]
  ring

private theorem raw_eq_sum (s : List Slot) (x : ℕ) :
    raw (s.map (atWidth x)) = (s.sublists.map (fun a => integralTerm a x)).sum := by
  simp only [raw,List.sublists_map,List.sum_eq_foldl]
  rw [List.foldl_map,List.foldl_map]
  simp only [fold_slots,List.length_map,integralTerm]

private theorem raw_affine (s : List Slot) (x : ℕ) :
    raw (s.map (atWidth x)) = raw (s.map (atWidth 0)) + (x : ℤ) *
      (raw (s.map (atWidth 1))-raw (s.map (atWidth 0))) := by
  simp only [raw_eq_sum]
  generalize s.sublists = rows
  induction rows with
  | nil => simp
  | cons boxes rows ih =>
    simp only [List.map_cons,List.sum_cons,term_affine boxes x,ih]
    ring

private def slots (j t : ℕ) (q : Shape) : List Slot :=
  let p : Shape := ⟨j+1,j,t⟩
  [((p,0),1), ((q,0),0), (bentGraph p,1),
    (bentLift (taylorLength-4) p,taylorLength-4),
    (bentLift (taylorLength-3) p,taylorLength-3)]

private theorem map_slots (j t x : ℕ) (q : Shape) :
    (slots j t q).map (atWidth x) =
      let p : Shape := ⟨j+1+x,j,t⟩
      [(p,0),(q,0),bentGraph p,bentLift (taylorLength-4) p,bentLift (taylorLength-3) p] := by
  simp [slots, atWidth, bentGraph, bentLift, Nat.add_mul, Nat.add_assoc,
    Nat.add_comm, Nat.add_left_comm, Nat.mul_comm]

private theorem raw_nonneg (j t x : ℕ) (q : Shape) (ht : 1≤t) (hj : 3*t+3≤j) :
    0 ≤ raw ((slots j t q).map (atWidth x)) := by
  rw [map_slots]
  let p : Shape := ⟨j+1+x,j,t⟩
  have hb : p.j ≤ p.b := by dsimp [p]; omega
  change 0 ≤ signedFive (p,0) (q,0) (bentGraph p) (bentLift (taylorLength-4) p)
    (bentLift (taylorLength-3) p)
  have hch : 3*p.t≤p.j := by dsimp [p]; omega
  exact signed_five_nonneg _ _ _ _ _ ⟨hb,hch,Nat.zero_le _⟩
    (Low48BentSupport.graph_chamber ht hj)
    (Low48BentSupport.lifted_chamber hb hj (by decide))
    (Low48BentSupport.lifted_chamber hb hj (by decide))

/-- Within one index and top degree, the tilted surface increases with width. -/
theorem tilted_width_mono (q : Shape) {b B j t : ℕ} (hb : j+1≤b) (hB : b≤B)
    (ht : 1≤t) (hj : 3*t+3≤j) :
    tiltedSurface (⟨b,j,t⟩ : Shape).chamber q ≤ tiltedSurface (⟨B,j,t⟩ : Shape).chamber q := by
  let s := slots j t q
  let f (x : ℕ) := raw (s.map (atWidth x))
  have ha (x : ℕ) : f x = f 0 + (x : ℤ) * (f 1-f 0) := raw_affine s x
  have hp (x : ℕ) : 0≤f x := raw_nonneg j t x q ht hj
  have hs : 0≤f 1-f 0 := by
    by_contra! h
    have hle : f 1-f 0 ≤ -1 := by omega
    let wid := (f 0).toNat+1
    have hwid : (wid : ℤ)=f 0+1 := by simp [wid,Int.toNat_of_nonneg (hp 0)]
    have hmul := mul_le_mul_of_nonneg_left hle (Int.natCast_nonneg wid)
    have hx := hp wid
    rw [ha wid,hwid] at hx
    rw [hwid] at hmul
    simp only [mul_neg,mul_one] at hmul
    omega
  have hr (a : ℕ) (h : j+1≤a) :
      tiltedSurface (⟨a,j,t⟩ : Shape).chamber q = (f (a-(j+1))).toNat := by
    have hmax : max a j = a := max_eq_left (by omega)
    have eq : j+1+(a-(j+1))=a := Nat.add_sub_of_le h
    simp only [f,s,map_slots,eq,tiltedSurface,Shape.chamber,hmax,ambientMix,raw]
  rw [hr _ hb,hr _ (hb.trans hB)]
  apply Int.toNat_le_toNat
  rw [ha (b-(j+1)),ha (B-(j+1))]
  have hw : ((b-(j+1) : ℕ) : ℤ) ≤ ((B-(j+1) : ℕ) : ℤ) := by
    exact_mod_cast Nat.sub_le_sub_right hB (j+1)
  exact add_le_add (le_refl (f 0)) (mul_le_mul_of_nonneg_right hw hs)

#print axioms tilted_width_mono
end Low6961WidthAffine
