import ProximityPrize.SubmissionLower.Z6970H2307PriceDefs
import ProximityPrize.SubmissionLower.Final50SurfaceLinearFive

set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 0
set_option maxRecDepth 30000

namespace Height2307PointRectangle
open K1_13 (Shape InBox ceilDiv)
open K1_13_8_2 (Chamber mixed_mono)
open Low6969RetainedCut (contractedPrice cutPrice fourSurface chamberHull residualBox hull_valid)
open Low6969Prices (physicalPrice physicalPriceOld)
open Low6969GeometryCut (chargedPrice)
open Low6969Monotone (box_refl normalize_mono normalize_chamber plus_mono plus_chamber scale_mono scale_chamber chart_mono chart_chamber)
open Low6969Monotone (box_refl normalize_mono normalize_chamber plus_mono plus_chamber
  scale_mono scale_chamber chart_mono chart_chamber)

/-- `physicalPriceOld` with the mixed surface numerator left free. -/
def charge (x : Shape) (l scale S : ℕ) : ℕ :=
  let p := x.chamber
  let q := Low6969Prices.primaryBox
  let h := K1_13.chart Low6969Prices.taylorLength p
  let numerator := ceilDiv S scale +
    ceilDiv ((Low6969Prices.errors + 2 * Low6969Prices.incidenceGap) * x.b * q.b *
      (K1_13.chart (Low6969Prices.taylorLength + 1) p).b) Low6969Prices.incidenceGap
  let auxBox := q.plus (p.scale 4)
  let curves := K1_13.mixed32 p q auxBox h + 2 * x.t * K1_13.mixed32 p p p h
  let points := K1_13.mixed32 p q auxBox p + 2 * x.t * K1_13.mixed32 p p p p
  ceilDiv numerator l + 2 * Low6969Prices.physicalDegree * x.b * q.b +
    ceilDiv (Low6969Prices.errors * curves + 2 * Low6969Prices.incidenceGap * points)
      (32 * Low6969Prices.incidenceGap)

theorem cut_eq (x : Shape) (l scale S : ℕ) : cutPrice x l scale S = charge x l scale S := by
  simp only [cutPrice, charge, chargedPrice, Low6969GeometryCut.auxCurves32,
    Low6969GeometryCut.auxPoints32, Low6969GeometryCut.membershipDegree, Nat.mul_assoc]
  rfl

theorem charge_mono {x y : Shape} (h : InBox x y) (hx : 3 * x.t ≤ x.j)
    (hy : 3 * y.t ≤ y.j) (l scale : ℕ) {S S' : ℕ} (hS : S ≤ S') : charge x l scale S ≤ charge y l scale S' := by
  let p := x.chamber
  let p' := y.chamber
  let q : Shape := Low6969Prices.primaryBox
  let L := Low6969Prices.taylorLength
  let A := q.plus (p.scale 4)
  let A' := q.plus (p'.scale 4)
  have hp := normalize_mono h
  have hpc : Chamber p := normalize_chamber x hx
  have hp'c : Chamber p' := normalize_chamber y hy
  have hqc : Chamber q := ⟨by decide, by decide⟩
  have ha : InBox A A' := plus_mono (box_refl q) (scale_mono hp 4)
  have hac : Chamber A := plus_chamber hqc (scale_chamber hpc 4)
  have ha'c : Chamber A' := plus_chamber hqc (scale_chamber hp'c 4)
  have hb := (chart_mono (L+1) hp).1
  have hmain : (Low6969Prices.errors + 2*Low6969Prices.incidenceGap) * x.b * q.b * (K1_13.chart (L+1) p).b ≤
      (Low6969Prices.errors + 2*Low6969Prices.incidenceGap) * y.b * q.b * (K1_13.chart (L+1) p').b := by
    have := h.1
    gcongr
  have hcurve := mixed_mono hp (box_refl q) ha (chart_mono L hp) hp'c hqc ha'c hqc hac (chart_chamber L p)
  have hpoint := mixed_mono hp (box_refl q) ha hp hp'c hqc ha'c hqc hac hpc
  have hcurve' := mixed_mono hp hp hp (chart_mono L hp) hp'c hp'c hp'c hpc hpc (chart_chamber L p)
  have hpoint' := mixed_mono hp hp hp hp hp'c hp'c hp'c hpc hpc hpc
  have htc := Nat.mul_le_mul_left 2 h.2.2
  have hc := Nat.add_le_add hcurve (Nat.mul_le_mul htc hcurve')
  have hn := Nat.add_le_add hpoint (Nat.mul_le_mul htc hpoint')
  have hgeom := Nat.add_le_add (Nat.mul_le_mul_left Low6969Prices.errors hc)
    (Nat.mul_le_mul_left (2*Low6969Prices.incidenceGap) hn)
  have hraw := Nat.mul_le_mul_right q.b (Nat.mul_le_mul_left (2*Low6969Prices.physicalDegree) h.1)
  exact Nat.add_le_add
    (Nat.add_le_add (Low6969Monotone.ceil_mono (Nat.add_le_add
      (Low6969Monotone.ceil_mono hS _) (Low6969Monotone.ceil_mono hmain _)) l) hraw)
    (Low6969Monotone.ceil_mono hgeom _)

end Height2307PointRectangle

namespace Height2307PointWidthAffine
open K1_13 (Shape)
open Low6969Prices (BentCap addBent bentIntegral ambientMix tiltedSurface tiltedFits
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

end Height2307PointWidthAffine

namespace Height2307PointFastPrice
open K1_13 (Shape mixed32 volume32 difference chart liftedChart ceilDiv)
open Low6969Prices (BentCap bentIntegral addBent ambientMix tiltedSurface bentGraph bentLift
  taylorLength primaryBox errors incidenceGap physicalDegree tiltedFits activeFitsPrice activeLoss
  activeClips surfaceNumerator32 physicalPriceOld physicalPriceWith physicalPriceTilted
  physicalPriceActive physicalPrice tiltedSurfaceActive)
def mixPos (pb pj pt qb qj qt rb rj rt sb sj st : ℕ) : ℕ :=
  16 * pb * qj * rj * st +
    16 * pb * qj * rt * sj +
    16 * pb * qt * rj * sj +
    144 * pb * qt * rt * st +
    16 * pj * qb * rj * st +
    16 * pj * qb * rt * sj +
    16 * pj * qj * rb * st +
    16 * pj * qj * rt * sb +
    56 * pj * qj * rt * st +
    16 * pj * qt * rb * sj +
    16 * pj * qt * rj * sb +
    56 * pj * qt * rj * st +
    56 * pj * qt * rt * sj +
    16 * pt * qb * rj * sj +
    144 * pt * qb * rt * st +
    16 * pt * qj * rb * sj +
    16 * pt * qj * rj * sb +
    56 * pt * qj * rj * st +
    56 * pt * qj * rt * sj +
    144 * pt * qt * rb * st +
    56 * pt * qt * rj * sj +
    144 * pt * qt * rt * sb +
    216 * pt * qt * rt * st
def mixNeg (pb pj pt qb qj qt rb rj rt sb sj st : ℕ) : ℕ :=
  48 * pb * qj * rt * st +
    48 * pb * qt * rj * st +
    48 * pb * qt * rt * sj +
    48 * pj * qb * rt * st +
    24 * pj * qj * rj * st +
    24 * pj * qj * rt * sj +
    48 * pj * qt * rb * st +
    24 * pj * qt * rj * sj +
    48 * pj * qt * rt * sb +
    120 * pj * qt * rt * st +
    48 * pt * qb * rj * st +
    48 * pt * qb * rt * sj +
    48 * pt * qj * rb * st +
    24 * pt * qj * rj * sj +
    48 * pt * qj * rt * sb +
    120 * pt * qj * rt * st +
    48 * pt * qt * rb * sj +
    48 * pt * qt * rj * sb +
    120 * pt * qt * rj * st +
    120 * pt * qt * rt * sj
def mix4 (pb pj pt qb qj qt rb rj rt sb sj st : ℕ) : ℕ :=
  mixPos pb pj pt qb qj qt rb rj rt sb sj st - mixNeg pb pj pt qb qj qt rb rj rt sb sj st
def mixF (p q r s : Shape) : ℕ :=
  mix4 p.b p.j p.t q.b q.j q.t r.b r.j r.t s.b s.j s.t
theorem mixF_eq (p q r s : Shape) : mixF p q r s = mixed32 p q r s := by
  obtain ⟨pb,pj,pt⟩ := p
  obtain ⟨qb,qj,qt⟩ := q
  obtain ⟨rb,rj,rt⟩ := r
  obtain ⟨sb,sj,st⟩ := s
  have key : difference (difference (difference (difference volume32 ⟨pb,pj,pt⟩) ⟨qb,qj,qt⟩)
      ⟨rb,rj,rt⟩) ⟨sb,sj,st⟩ ⟨0,0,0⟩ = (mixPos pb pj pt qb qj qt rb rj rt sb sj st : ℤ) -
        (mixNeg pb pj pt qb qj qt rb rj rt sb sj st : ℤ) := by
    simp only [difference, volume32, K1_13.Shape.plus, mixPos, mixNeg]
    push_cast
    ring
  unfold mixF mix4 mixed32
  dsimp only
  rw [key]
  omega
def bentPos (B J T H : ℕ) : ℕ :=
  H * (160*T^2*H^2 + 540*T^4 + 960*J*H^3 + 960*J*T^2*H + 840*J^2*T^2 + 240*J^3*H +
    640*B*T*H^2 + 1440*B*T^3 + 640*B*J*H^2 + 960*B*J*T*H + 480*B*J^2*T)
def bentNeg (B J T H : ℕ) : ℕ :=
  H * (576*H^4 + 480*T^3*H + 320*J*T*H^2 + 1200*J*T^3 + 480*J^2*H^2 + 480*J^2*T*H +
    240*J^3*T + 960*B*H^3 + 1440*B*T^2*H + 1440*B*J*T^2 + 480*B*J^2*H)
theorem bent_eq (B J T H : ℕ) :
    bentIntegral B J T H = (bentPos B J T H : ℤ) - (bentNeg B J T H : ℤ) := by
  simp only [bentIntegral, bentPos, bentNeg]
  push_cast
  ring
def mixStep (acc : ℕ × ℕ) (boxes : List BentCap) : ℕ × ℕ :=
  let s := boxes.foldl addBent (⟨0,0,0⟩, 0)
  let a := bentPos s.1.b s.1.j s.1.t s.2
  let n := bentNeg s.1.b s.1.j s.1.t s.2
  if (5 - boxes.length) % 2 = 0 then (acc.1 + a, acc.2 + n) else (acc.1 + n, acc.2 + a)
def ambientMixF (caps : List BentCap) : ℕ :=
  let r := caps.sublists.foldl mixStep (0,0)
  r.1 - r.2
private theorem fold_eq (Ls : List (List BentCap)) (a : ℤ) (acc : ℕ × ℕ)
    (h : a = acc.1 - acc.2) :
    Ls.foldl (fun acc boxes =>
      let s := boxes.foldl addBent (⟨0,0,0⟩, 0)
      acc + (-1 : ℤ) ^ (5 - boxes.length) * bentIntegral s.1.b s.1.j s.1.t s.2) a =
      ((Ls.foldl mixStep acc).1 : ℤ) - (Ls.foldl mixStep acc).2 := by
  induction Ls generalizing a acc with
  | nil => simpa using h
  | cons boxes rest ih =>
    simp only [List.foldl_cons]
    apply ih
    rw [bent_eq, h, neg_one_pow_eq_pow_mod_two]
    rcases Nat.mod_two_eq_zero_or_one (5 - boxes.length) with e | e
    · simp only [mixStep, e, ↓reduceIte, pow_zero, one_mul]
      push_cast; ring
    · simp only [mixStep, e, Nat.one_ne_zero, ↓reduceIte, pow_one]
      push_cast; ring
theorem ambientMix_eq (caps : List BentCap) : ambientMix caps = ambientMixF caps := by
  have key := fold_eq caps.sublists 0 (0,0) (by simp)
  unfold ambientMix ambientMixF
  dsimp only at key ⊢
  rw [key]
  omega
def tiltFRef (p q : Shape) : ℕ :=
  ambientMixF [(p, 0), (q, 0), bentGraph p,
    bentLift (taylorLength - 4) p, bentLift (taylorLength - 3) p]
theorem tiltFRef_eq (p q : Shape) : tiltFRef p q = tiltedSurface p q := by
  unfold tiltFRef tiltedSurface
  rw [ambientMix_eq]
/-! Kernel-friendly unrolled evaluator for the five-cap inclusion-exclusion. -/
def bentPosN (B J T H : ℕ) : ℕ := Nat.mul H (Nat.add (Nat.mul T (Nat.add (Nat.mul T (Nat.add (Nat.mul H (Nat.add (Nat.mul H (160)) (Nat.mul J (960)))) (Nat.add (Nat.mul T (Nat.add (Nat.mul T (540)) (Nat.mul B (1440)))) (Nat.mul J (Nat.mul J (840)))))) (Nat.mul B (Nat.add (Nat.mul H (Nat.add (Nat.mul H (640)) (Nat.mul J (960)))) (Nat.mul J (Nat.mul J (480))))))) (Nat.mul H (Nat.mul J (Nat.add (Nat.mul H (Nat.add (Nat.mul H (960)) (Nat.mul B (640)))) (Nat.mul J (Nat.mul J (240)))))))
def bentNegN (B J T H : ℕ) : ℕ := Nat.mul H (Nat.add (Nat.mul H (Nat.add (Nat.mul H (Nat.add (Nat.mul H (Nat.add (Nat.mul H (576)) (Nat.mul B (960)))) (Nat.mul J (Nat.add (Nat.mul T (320)) (Nat.mul J (480)))))) (Nat.add (Nat.mul T (Nat.add (Nat.mul T (Nat.add (Nat.mul T (480)) (Nat.mul B (1440)))) (Nat.mul J (Nat.mul J (480))))) (Nat.mul J (Nat.mul J (Nat.mul B (480))))))) (Nat.mul T (Nat.mul J (Nat.add (Nat.mul T (Nat.add (Nat.mul T (1200)) (Nat.mul B (1440)))) (Nat.mul J (Nat.mul J (240)))))))
def ambN (fa fn : ℕ → ℕ → ℕ → ℕ → ℕ) (b0 j0 t0 h0 b1 j1 t1 h1 b2 j2 t2 h2 b3 j3 t3 h3 b4 j4 t4 h4 : ℕ) : ℕ :=
  Nat.sub (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add 0 (fn 0 0 0 0)) (fa (Nat.add 0 b0) (Nat.add 0 j0) (Nat.add 0 t0) (Nat.add 0 h0))) (fa (Nat.add 0 b1) (Nat.add 0 j1) (Nat.add 0 t1) (Nat.add 0 h1))) (fn (Nat.add (Nat.add 0 b0) b1) (Nat.add (Nat.add 0 j0) j1) (Nat.add (Nat.add 0 t0) t1) (Nat.add (Nat.add 0 h0) h1))) (fa (Nat.add 0 b2) (Nat.add 0 j2) (Nat.add 0 t2) (Nat.add 0 h2))) (fn (Nat.add (Nat.add 0 b0) b2) (Nat.add (Nat.add 0 j0) j2) (Nat.add (Nat.add 0 t0) t2) (Nat.add (Nat.add 0 h0) h2))) (fn (Nat.add (Nat.add 0 b1) b2) (Nat.add (Nat.add 0 j1) j2) (Nat.add (Nat.add 0 t1) t2) (Nat.add (Nat.add 0 h1) h2))) (fa (Nat.add (Nat.add (Nat.add 0 b0) b1) b2) (Nat.add (Nat.add (Nat.add 0 j0) j1) j2) (Nat.add (Nat.add (Nat.add 0 t0) t1) t2) (Nat.add (Nat.add (Nat.add 0 h0) h1) h2))) (fa (Nat.add 0 b3) (Nat.add 0 j3) (Nat.add 0 t3) (Nat.add 0 h3))) (fn (Nat.add (Nat.add 0 b0) b3) (Nat.add (Nat.add 0 j0) j3) (Nat.add (Nat.add 0 t0) t3) (Nat.add (Nat.add 0 h0) h3))) (fn (Nat.add (Nat.add 0 b1) b3) (Nat.add (Nat.add 0 j1) j3) (Nat.add (Nat.add 0 t1) t3) (Nat.add (Nat.add 0 h1) h3))) (fa (Nat.add (Nat.add (Nat.add 0 b0) b1) b3) (Nat.add (Nat.add (Nat.add 0 j0) j1) j3) (Nat.add (Nat.add (Nat.add 0 t0) t1) t3) (Nat.add (Nat.add (Nat.add 0 h0) h1) h3))) (fn (Nat.add (Nat.add 0 b2) b3) (Nat.add (Nat.add 0 j2) j3) (Nat.add (Nat.add 0 t2) t3) (Nat.add (Nat.add 0 h2) h3))) (fa (Nat.add (Nat.add (Nat.add 0 b0) b2) b3) (Nat.add (Nat.add (Nat.add 0 j0) j2) j3) (Nat.add (Nat.add (Nat.add 0 t0) t2) t3) (Nat.add (Nat.add (Nat.add 0 h0) h2) h3))) (fa (Nat.add (Nat.add (Nat.add 0 b1) b2) b3) (Nat.add (Nat.add (Nat.add 0 j1) j2) j3) (Nat.add (Nat.add (Nat.add 0 t1) t2) t3) (Nat.add (Nat.add (Nat.add 0 h1) h2) h3))) (fn (Nat.add (Nat.add (Nat.add (Nat.add 0 b0) b1) b2) b3) (Nat.add (Nat.add (Nat.add (Nat.add 0 j0) j1) j2) j3) (Nat.add (Nat.add (Nat.add (Nat.add 0 t0) t1) t2) t3) (Nat.add (Nat.add (Nat.add (Nat.add 0 h0) h1) h2) h3))) (fa (Nat.add 0 b4) (Nat.add 0 j4) (Nat.add 0 t4) (Nat.add 0 h4))) (fn (Nat.add (Nat.add 0 b0) b4) (Nat.add (Nat.add 0 j0) j4) (Nat.add (Nat.add 0 t0) t4) (Nat.add (Nat.add 0 h0) h4))) (fn (Nat.add (Nat.add 0 b1) b4) (Nat.add (Nat.add 0 j1) j4) (Nat.add (Nat.add 0 t1) t4) (Nat.add (Nat.add 0 h1) h4))) (fa (Nat.add (Nat.add (Nat.add 0 b0) b1) b4) (Nat.add (Nat.add (Nat.add 0 j0) j1) j4) (Nat.add (Nat.add (Nat.add 0 t0) t1) t4) (Nat.add (Nat.add (Nat.add 0 h0) h1) h4))) (fn (Nat.add (Nat.add 0 b2) b4) (Nat.add (Nat.add 0 j2) j4) (Nat.add (Nat.add 0 t2) t4) (Nat.add (Nat.add 0 h2) h4))) (fa (Nat.add (Nat.add (Nat.add 0 b0) b2) b4) (Nat.add (Nat.add (Nat.add 0 j0) j2) j4) (Nat.add (Nat.add (Nat.add 0 t0) t2) t4) (Nat.add (Nat.add (Nat.add 0 h0) h2) h4))) (fa (Nat.add (Nat.add (Nat.add 0 b1) b2) b4) (Nat.add (Nat.add (Nat.add 0 j1) j2) j4) (Nat.add (Nat.add (Nat.add 0 t1) t2) t4) (Nat.add (Nat.add (Nat.add 0 h1) h2) h4))) (fn (Nat.add (Nat.add (Nat.add (Nat.add 0 b0) b1) b2) b4) (Nat.add (Nat.add (Nat.add (Nat.add 0 j0) j1) j2) j4) (Nat.add (Nat.add (Nat.add (Nat.add 0 t0) t1) t2) t4) (Nat.add (Nat.add (Nat.add (Nat.add 0 h0) h1) h2) h4))) (fn (Nat.add (Nat.add 0 b3) b4) (Nat.add (Nat.add 0 j3) j4) (Nat.add (Nat.add 0 t3) t4) (Nat.add (Nat.add 0 h3) h4))) (fa (Nat.add (Nat.add (Nat.add 0 b0) b3) b4) (Nat.add (Nat.add (Nat.add 0 j0) j3) j4) (Nat.add (Nat.add (Nat.add 0 t0) t3) t4) (Nat.add (Nat.add (Nat.add 0 h0) h3) h4))) (fa (Nat.add (Nat.add (Nat.add 0 b1) b3) b4) (Nat.add (Nat.add (Nat.add 0 j1) j3) j4) (Nat.add (Nat.add (Nat.add 0 t1) t3) t4) (Nat.add (Nat.add (Nat.add 0 h1) h3) h4))) (fn (Nat.add (Nat.add (Nat.add (Nat.add 0 b0) b1) b3) b4) (Nat.add (Nat.add (Nat.add (Nat.add 0 j0) j1) j3) j4) (Nat.add (Nat.add (Nat.add (Nat.add 0 t0) t1) t3) t4) (Nat.add (Nat.add (Nat.add (Nat.add 0 h0) h1) h3) h4))) (fa (Nat.add (Nat.add (Nat.add 0 b2) b3) b4) (Nat.add (Nat.add (Nat.add 0 j2) j3) j4) (Nat.add (Nat.add (Nat.add 0 t2) t3) t4) (Nat.add (Nat.add (Nat.add 0 h2) h3) h4))) (fn (Nat.add (Nat.add (Nat.add (Nat.add 0 b0) b2) b3) b4) (Nat.add (Nat.add (Nat.add (Nat.add 0 j0) j2) j3) j4) (Nat.add (Nat.add (Nat.add (Nat.add 0 t0) t2) t3) t4) (Nat.add (Nat.add (Nat.add (Nat.add 0 h0) h2) h3) h4))) (fn (Nat.add (Nat.add (Nat.add (Nat.add 0 b1) b2) b3) b4) (Nat.add (Nat.add (Nat.add (Nat.add 0 j1) j2) j3) j4) (Nat.add (Nat.add (Nat.add (Nat.add 0 t1) t2) t3) t4) (Nat.add (Nat.add (Nat.add (Nat.add 0 h1) h2) h3) h4))) (fa (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add 0 b0) b1) b2) b3) b4) (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add 0 j0) j1) j2) j3) j4) (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add 0 t0) t1) t2) t3) t4) (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add 0 h0) h1) h2) h3) h4)))
    (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add 0 (fa 0 0 0 0)) (fn (Nat.add 0 b0) (Nat.add 0 j0) (Nat.add 0 t0) (Nat.add 0 h0))) (fn (Nat.add 0 b1) (Nat.add 0 j1) (Nat.add 0 t1) (Nat.add 0 h1))) (fa (Nat.add (Nat.add 0 b0) b1) (Nat.add (Nat.add 0 j0) j1) (Nat.add (Nat.add 0 t0) t1) (Nat.add (Nat.add 0 h0) h1))) (fn (Nat.add 0 b2) (Nat.add 0 j2) (Nat.add 0 t2) (Nat.add 0 h2))) (fa (Nat.add (Nat.add 0 b0) b2) (Nat.add (Nat.add 0 j0) j2) (Nat.add (Nat.add 0 t0) t2) (Nat.add (Nat.add 0 h0) h2))) (fa (Nat.add (Nat.add 0 b1) b2) (Nat.add (Nat.add 0 j1) j2) (Nat.add (Nat.add 0 t1) t2) (Nat.add (Nat.add 0 h1) h2))) (fn (Nat.add (Nat.add (Nat.add 0 b0) b1) b2) (Nat.add (Nat.add (Nat.add 0 j0) j1) j2) (Nat.add (Nat.add (Nat.add 0 t0) t1) t2) (Nat.add (Nat.add (Nat.add 0 h0) h1) h2))) (fn (Nat.add 0 b3) (Nat.add 0 j3) (Nat.add 0 t3) (Nat.add 0 h3))) (fa (Nat.add (Nat.add 0 b0) b3) (Nat.add (Nat.add 0 j0) j3) (Nat.add (Nat.add 0 t0) t3) (Nat.add (Nat.add 0 h0) h3))) (fa (Nat.add (Nat.add 0 b1) b3) (Nat.add (Nat.add 0 j1) j3) (Nat.add (Nat.add 0 t1) t3) (Nat.add (Nat.add 0 h1) h3))) (fn (Nat.add (Nat.add (Nat.add 0 b0) b1) b3) (Nat.add (Nat.add (Nat.add 0 j0) j1) j3) (Nat.add (Nat.add (Nat.add 0 t0) t1) t3) (Nat.add (Nat.add (Nat.add 0 h0) h1) h3))) (fa (Nat.add (Nat.add 0 b2) b3) (Nat.add (Nat.add 0 j2) j3) (Nat.add (Nat.add 0 t2) t3) (Nat.add (Nat.add 0 h2) h3))) (fn (Nat.add (Nat.add (Nat.add 0 b0) b2) b3) (Nat.add (Nat.add (Nat.add 0 j0) j2) j3) (Nat.add (Nat.add (Nat.add 0 t0) t2) t3) (Nat.add (Nat.add (Nat.add 0 h0) h2) h3))) (fn (Nat.add (Nat.add (Nat.add 0 b1) b2) b3) (Nat.add (Nat.add (Nat.add 0 j1) j2) j3) (Nat.add (Nat.add (Nat.add 0 t1) t2) t3) (Nat.add (Nat.add (Nat.add 0 h1) h2) h3))) (fa (Nat.add (Nat.add (Nat.add (Nat.add 0 b0) b1) b2) b3) (Nat.add (Nat.add (Nat.add (Nat.add 0 j0) j1) j2) j3) (Nat.add (Nat.add (Nat.add (Nat.add 0 t0) t1) t2) t3) (Nat.add (Nat.add (Nat.add (Nat.add 0 h0) h1) h2) h3))) (fn (Nat.add 0 b4) (Nat.add 0 j4) (Nat.add 0 t4) (Nat.add 0 h4))) (fa (Nat.add (Nat.add 0 b0) b4) (Nat.add (Nat.add 0 j0) j4) (Nat.add (Nat.add 0 t0) t4) (Nat.add (Nat.add 0 h0) h4))) (fa (Nat.add (Nat.add 0 b1) b4) (Nat.add (Nat.add 0 j1) j4) (Nat.add (Nat.add 0 t1) t4) (Nat.add (Nat.add 0 h1) h4))) (fn (Nat.add (Nat.add (Nat.add 0 b0) b1) b4) (Nat.add (Nat.add (Nat.add 0 j0) j1) j4) (Nat.add (Nat.add (Nat.add 0 t0) t1) t4) (Nat.add (Nat.add (Nat.add 0 h0) h1) h4))) (fa (Nat.add (Nat.add 0 b2) b4) (Nat.add (Nat.add 0 j2) j4) (Nat.add (Nat.add 0 t2) t4) (Nat.add (Nat.add 0 h2) h4))) (fn (Nat.add (Nat.add (Nat.add 0 b0) b2) b4) (Nat.add (Nat.add (Nat.add 0 j0) j2) j4) (Nat.add (Nat.add (Nat.add 0 t0) t2) t4) (Nat.add (Nat.add (Nat.add 0 h0) h2) h4))) (fn (Nat.add (Nat.add (Nat.add 0 b1) b2) b4) (Nat.add (Nat.add (Nat.add 0 j1) j2) j4) (Nat.add (Nat.add (Nat.add 0 t1) t2) t4) (Nat.add (Nat.add (Nat.add 0 h1) h2) h4))) (fa (Nat.add (Nat.add (Nat.add (Nat.add 0 b0) b1) b2) b4) (Nat.add (Nat.add (Nat.add (Nat.add 0 j0) j1) j2) j4) (Nat.add (Nat.add (Nat.add (Nat.add 0 t0) t1) t2) t4) (Nat.add (Nat.add (Nat.add (Nat.add 0 h0) h1) h2) h4))) (fa (Nat.add (Nat.add 0 b3) b4) (Nat.add (Nat.add 0 j3) j4) (Nat.add (Nat.add 0 t3) t4) (Nat.add (Nat.add 0 h3) h4))) (fn (Nat.add (Nat.add (Nat.add 0 b0) b3) b4) (Nat.add (Nat.add (Nat.add 0 j0) j3) j4) (Nat.add (Nat.add (Nat.add 0 t0) t3) t4) (Nat.add (Nat.add (Nat.add 0 h0) h3) h4))) (fn (Nat.add (Nat.add (Nat.add 0 b1) b3) b4) (Nat.add (Nat.add (Nat.add 0 j1) j3) j4) (Nat.add (Nat.add (Nat.add 0 t1) t3) t4) (Nat.add (Nat.add (Nat.add 0 h1) h3) h4))) (fa (Nat.add (Nat.add (Nat.add (Nat.add 0 b0) b1) b3) b4) (Nat.add (Nat.add (Nat.add (Nat.add 0 j0) j1) j3) j4) (Nat.add (Nat.add (Nat.add (Nat.add 0 t0) t1) t3) t4) (Nat.add (Nat.add (Nat.add (Nat.add 0 h0) h1) h3) h4))) (fn (Nat.add (Nat.add (Nat.add 0 b2) b3) b4) (Nat.add (Nat.add (Nat.add 0 j2) j3) j4) (Nat.add (Nat.add (Nat.add 0 t2) t3) t4) (Nat.add (Nat.add (Nat.add 0 h2) h3) h4))) (fa (Nat.add (Nat.add (Nat.add (Nat.add 0 b0) b2) b3) b4) (Nat.add (Nat.add (Nat.add (Nat.add 0 j0) j2) j3) j4) (Nat.add (Nat.add (Nat.add (Nat.add 0 t0) t2) t3) t4) (Nat.add (Nat.add (Nat.add (Nat.add 0 h0) h2) h3) h4))) (fa (Nat.add (Nat.add (Nat.add (Nat.add 0 b1) b2) b3) b4) (Nat.add (Nat.add (Nat.add (Nat.add 0 j1) j2) j3) j4) (Nat.add (Nat.add (Nat.add (Nat.add 0 t1) t2) t3) t4) (Nat.add (Nat.add (Nat.add (Nat.add 0 h1) h2) h3) h4))) (fn (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add 0 b0) b1) b2) b3) b4) (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add 0 j0) j1) j2) j3) j4) (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add 0 t0) t1) t2) t3) t4) (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add 0 h0) h1) h2) h3) h4)))
theorem bentPosN_eq (B J T H : ℕ) : bentPosN B J T H = bentPos B J T H := by
  unfold bentPosN bentPos
  simp only [Nat.add_eq, Nat.mul_eq]
  ring
theorem bentNegN_eq (B J T H : ℕ) : bentNegN B J T H = bentNeg B J T H := by
  unfold bentNegN bentNeg
  simp only [Nat.add_eq, Nat.mul_eq]
  ring
set_option maxRecDepth 100000 in
theorem ambN_ref (c0 c1 c2 c3 c4 : BentCap) :
    ambientMixF [c0,c1,c2,c3,c4] = ambN bentPos bentNeg c0.1.b c0.1.j c0.1.t c0.2 c1.1.b c1.1.j c1.1.t c1.2
      c2.1.b c2.1.j c2.1.t c2.2 c3.1.b c3.1.j c3.1.t c3.2 c4.1.b c4.1.j c4.1.t c4.2 := by
  with_unfolding_all exact rfl
def tiltF (p q : Shape) : ℕ :=
  ambN bentPosN bentNegN p.b p.j p.t 0 q.b q.j q.t 0
    (bentGraph p).1.b (bentGraph p).1.j (bentGraph p).1.t (bentGraph p).2
    (bentLift (taylorLength - 4) p).1.b (bentLift (taylorLength - 4) p).1.j (bentLift (taylorLength - 4) p).1.t (bentLift (taylorLength - 4) p).2
    (bentLift (taylorLength - 3) p).1.b (bentLift (taylorLength - 3) p).1.j (bentLift (taylorLength - 3) p).1.t (bentLift (taylorLength - 3) p).2
theorem tiltF_eq (p q : Shape) : tiltF p q = tiltedSurface p q := by
  rw [← tiltFRef_eq]
  unfold tiltF tiltFRef
  rw [ambN_ref]
  have h1 : bentPosN = bentPos := funext fun a => funext fun b => funext fun c => funext fun d => bentPosN_eq a b c d
  have h2 : bentNegN = bentNeg := funext fun a => funext fun b => funext fun c => funext fun d => bentNegN_eq a b c d
  rw [h1, h2]
def surfaceNumerator32F (p q : Shape) : ℕ :=
  let L := taylorLength
  let g : Shape := ⟨max p.b (p.j + 1), p.j + 1, min (p.t + 1) ((p.j + 1) / 3)⟩
  let a := liftedChart (L + 1) p
  let b := liftedChart (L + 2) p
  min (mixF p q (chart (L + 1) p) (chart (L + 2) p))
    (mixF p q a b + (L + 1) * mixF p q g b + (L + 2) * mixF p q g a)
def physicalPriceOldF (x : Shape) (l : ℕ) : ℕ :=
  let p := x.chamber
  let q := primaryBox
  let h := chart taylorLength p
  let numerator := ceilDiv (surfaceNumerator32F p q) 32 +
    ceilDiv ((errors + 2 * incidenceGap) * x.b * q.b * (chart (taylorLength + 1) p).b)
      incidenceGap
  let auxBox := q.plus (p.scale 4)
  let curves := mixF p q auxBox h + 2 * x.t * mixF p p p h
  let points := mixF p q auxBox p + 2 * x.t * mixF p p p p
  ceilDiv numerator l + 2 * physicalDegree * x.b * q.b +
    ceilDiv (errors * curves + 2 * incidenceGap * points) (32 * incidenceGap)
def physicalPriceWithF (x : Shape) (l surface : ℕ) : ℕ :=
  let p := x.chamber
  let q := primaryBox
  let h := chart taylorLength p
  let numerator := ceilDiv surface (60 * 32) +
    ceilDiv ((errors + 2 * incidenceGap) * x.b * q.b * (chart (taylorLength + 1) p).b)
      incidenceGap
  let auxBox := q.plus (p.scale 4)
  let curves := mixF p q auxBox h + 2 * x.t * mixF p p p h
  let points := mixF p q auxBox p + 2 * x.t * mixF p p p p
  ceilDiv numerator l + 2 * physicalDegree * x.b * q.b +
    ceilDiv (errors * curves + 2 * incidenceGap * points) (32 * incidenceGap)
def physicalPriceF (x : Shape) (l K : ℕ) : ℕ :=
  if tiltedFits x then
    let base := min (physicalPriceOldF x l) (physicalPriceWithF x l (tiltF x.chamber primaryBox))
    if activeFitsPrice x K then
      min base (physicalPriceWithF x l (tiltF x.chamber primaryBox - activeLoss (activeClips x.chamber K)))
    else base
  else physicalPriceOldF x l
theorem physicalPriceOldF_eq (x : Shape) (l : ℕ) : physicalPriceOldF x l = physicalPriceOld x l := by
  simp only [physicalPriceOldF, physicalPriceOld, surfaceNumerator32F, surfaceNumerator32, mixF_eq]
theorem physicalPriceWithF_eq (x : Shape) (l s : ℕ) : physicalPriceWithF x l s = physicalPriceWith x l s := by
  simp only [physicalPriceWithF, physicalPriceWith, mixF_eq]
theorem physicalPriceF_eq (x : Shape) (l K : ℕ) : physicalPriceF x l K = physicalPrice x l K := by
  simp only [physicalPriceF, physicalPrice, physicalPriceTilted, physicalPriceActive,
    tiltedSurfaceActive, physicalPriceOldF_eq, physicalPriceWithF_eq, tiltF_eq]
def chargeF (x : Shape) (l scale S : ℕ) : ℕ :=
  let p := x.chamber
  let q := primaryBox
  let h := chart taylorLength p
  let numerator := ceilDiv S scale +
    ceilDiv ((errors + 2 * incidenceGap) * x.b * q.b *
      (chart (taylorLength + 1) p).b) incidenceGap
  let auxBox := q.plus (p.scale 4)
  let curves := mixF p q auxBox h + 2 * x.t * mixF p p p h
  let points := mixF p q auxBox p + 2 * x.t * mixF p p p p
  ceilDiv numerator l + 2 * physicalDegree * x.b * q.b +
    ceilDiv (errors * curves + 2 * incidenceGap * points) (32 * incidenceGap)
theorem chargeF_eq (x : Shape) (l scale S : ℕ) :
    chargeF x l scale S = Low6969RetainedCut.cutPrice x l scale S := by
  rw [Height2307PointRectangle.cut_eq]
  simp only [chargeF, Height2307PointRectangle.charge, mixF_eq]
def fourSurfaceF (p q : Shape) : ℕ :=
  mixF p q (chart (taylorLength+1) p) (chart (taylorLength+2) p)
theorem fourSurfaceF_eq (p q : Shape) : fourSurfaceF p q = Low6969RetainedCut.fourSurface p q := by
  simp only [fourSurfaceF, Low6969RetainedCut.fourSurface, mixF_eq]
def contractedPriceF (x h : Shape) (l active : ℕ) : ℕ :=
  let q := Low6969RetainedCut.chamberHull (Low6969RetainedCut.residualBox h l)
  let old := physicalPriceF x l active
  let four := if 0 < q.t then min old (chargeF x l 32 (fourSurfaceF x.chamber q)) else old
  if tiltedFits x then min four (chargeF x l (60*32) (tiltF x.chamber q)) else four
theorem contractedPriceF_eq (x h : Shape) (l active : ℕ) :
    contractedPriceF x h l active = Low6969RetainedCut.contractedPrice x h l active := by
  simp only [contractedPriceF, Low6969RetainedCut.contractedPrice, physicalPriceF_eq, chargeF_eq,
    fourSurfaceF_eq, tiltF_eq]
open Low6969SharedPrice (Surface Rate surfaceScale coord expression deficit slope)
def surfaceF (kind : Surface) (f q : Shape) : ℕ :=
  match kind with
  | .ordinary =>
    let p := f.chamber
    mixF p q (chart (taylorLength + 1) p) (chart (taylorLength + 2) p)
  | .tilted => tiltF f.chamber q
theorem surfaceF_eq (kind : Surface) (f q : Shape) :
    surfaceF kind f q = Low6969SharedPrice.surface kind f q := by
  cases kind <;> simp only [surfaceF, Low6969SharedPrice.surface, mixF_eq, tiltF_eq]
def weightsF (kind : Surface) (f : Shape) : Shape :=
  let b := surfaceF kind f ⟨1,0,0⟩
  let j := surfaceF kind f ⟨1,1,0⟩ - b
  let t := surfaceF kind f ⟨3,3,1⟩ - 3 * (b+j)
  ⟨b,j,t⟩
theorem weightsF_eq (kind : Surface) (f : Shape) :
    weightsF kind f = Low6969SharedPrice.weights kind f := by
  simp only [weightsF, Low6969SharedPrice.weights, surfaceF_eq]
def RateFitsF (f : Shape) (u : Rate) : Prop :=
  let p := coord slope u.pivot
  let q := coord f u.pivot
  let w := weightsF u.kind f
  let target := 3 * surfaceScale u.kind * u.amount
  (u.kind = .tilted → tiltedFits f) ∧
  0 < u.split ∧ u.split*p < q ∧
  (∀ i, p * coord f i ≤ q * coord slope i) ∧
  (∀ useIndex : Bool, expression w slope useIndex u.topIndex ≤ target) ∧
  (∀ useIndex : Bool, expression w (deficit q p f) useIndex u.topIndex ≤ target*(q-u.split*p))
instance (f : Shape) (u : Rate) : Decidable (RateFitsF f u) := by
  unfold RateFitsF
  infer_instance
theorem rateFitsF_iff (f : Shape) (u : Rate) : RateFitsF f u ↔ Low6969SharedPrice.RateFits f u := by
  simp only [RateFitsF, Low6969SharedPrice.RateFits, weightsF_eq]
def additiveBaseF (x : Shape) (l : ℕ) : ℕ :=
  let p := x.chamber
  let q := primaryBox
  let h := chart taylorLength p
  let h1 := chart (taylorLength+1) p
  let cont := ceilDiv ((errors+2*incidenceGap)*x.b*q.b*h1.b) incidenceGap
  let z := q.plus (p.scale 4)
  let cv := mixF p q z h + 2*x.t*mixF p p p h
  let pt := mixF p q z p + 2*x.t*mixF p p p p
  ceilDiv cont l + 2*physicalDegree*x.b*q.b +
    ceilDiv (errors*cv+2*incidenceGap*pt) (32*incidenceGap)
def priceF (x : Shape) (l K : ℕ) (u : Rate) : ℕ :=
  ceilDiv (physicalPriceF x l K + u.split*additiveBaseF x l + u.split*u.amount + 1)
    (u.split+1) + Low6969SharedPrice.nonsharedFee x l
theorem priceF_eq (x : Shape) (l K : ℕ) (u : Rate) :
    priceF x l K u = Low6969SharedPrice.price x l K u := by
  simp only [priceF, Low6969SharedPrice.price, Low6969SharedPrice.additiveBase, additiveBaseF,
    physicalPriceF_eq, mixF_eq]

theorem additiveBaseF_eq (x : Shape) (l : ℕ) : additiveBaseF x l = Low6969SharedPrice.additiveBase x l := by
  simp only [additiveBaseF, Low6969SharedPrice.additiveBase, mixF_eq]

end Height2307PointFastPrice
