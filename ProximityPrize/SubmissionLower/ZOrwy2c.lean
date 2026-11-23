import ProximityPrize.SubmissionLower.Z3vxfLe
set_option Elab.async false
open _root_ renaming Int.natCast_nonneg → zbO, Nat.add_le_add → z9f, Nat.add_le_add_right → zlr, Nat.mul_le_mul_right → ztf, Nat.sub_le_sub_right → zIu
section
set_option autoImplicit true
namespace q2w4Sxc
open aR (Shape aO)
open P6_6 P6_6_8
open yi (bF tD)
open nZ (j0 On Jg DC A9 ZT)
open private bhj from ProximityPrize.SubmissionLower.CH
private theorem weighted_chamber (L:ℕ) (p:Shape) :bF (weightedChart L p) := by
  unfold weightedChart
  split
  · exact ⟨le_max_right _ _,ZT _ _⟩
  · exact A9 L p
private theorem weighted_mono {p P:Shape} (h:aO p P) (ht:p.t=1↔P.t=1) (L:ℕ) :
    aO (weightedChart L p) (weightedChart L P) := by
  by_cases hp:p.t=1
  · have hj:3+(L-4)*(p.j - 2)≤3+(L-4)*(P.j - 2) := by gcongr; exact h.2.1
    have hb:1+(L-4)*(p.b - 1)≤1+(L-4)*(P.b - 1) := by gcongr; exact h.1
    simp only [weightedChart,ite_eq_left hp,ite_eq_left (ht.mp hp)]
    exact ⟨max_le_max hb hj,hj,min_le_min_left _ (Nat.div_le_div_right hj)⟩
  · simpa only [weightedChart,ite_eq_right hp,ite_eq_right (mt ht.mpr hp)] using DC L h
private theorem physical_chamber (v :Shape) (k :ℕ) :bF (physicalBody v k) := by
  apply Jg
  let y :=rawResidual Wk (v.scale k)
  let d:=min y.j (3*y.b)
  change 3*min y.t (min y.b (d/3))≤d
  have h:=(min_le_right y.t _).trans (min_le_right y.b (d/3))
  omega
private theorem join_chamber {p q:Shape} (hp:bF p) (hq:bF q) :
    bF (joinBody p q) := by
  refine ⟨max_le_max hp.1 hq.1,?_⟩
  obtain h | h:=le_total p.t q.t
  · exact (show 3*max p.t q.t≤q.j by rw [max_eq_right h]; exact hq.2).trans (le_max_right _ _)
  · exact (show 3*max p.t q.t≤p.j by rw [max_eq_left h]; exact hp.2).trans (le_max_left _ _)
private theorem mix_le {a A q s S w W:Shape} (ha :aO a A) (hs :aO s S) (hw:aO w W)
    (hA:bF A) (hq:bF q) (hS:bF S)
    (hs' : bF s) (hw' : bF w) (hW:bF W) :
    wP a q s w≤wP A q S W:= by
  rw [← bhj a q s w hq hs' hw',← bhj A q S W hq hS hW]
  exact Int.ofNat_le.mpr (tD ha (j0 _) hs hw hA hq hS hq hs' hw')
private theorem mix_nonneg (a q s w:Shape) (hq:bF q) (hs :bF s) (hw:bF w) :
    0≤wP a q s w:= by
  rw [← bhj a q s w hq hs hw]
  exact zbO _
private theorem curve_le {q p P s S:Shape}
    (hq:bF q) (hp:bF p) (hP:bF P)
    (hs :bF s) (hS:bF S) (h:aO p P) (h' : aO s S) (ht:p.t=1↔P.t=1) :
    curve32 p p q s≤ curve32 P P q S:= by
  unfold curve32
  exact add_le_add (mul_le_mul_of_nonneg_left
      (mix_le h h' (weighted_mono h ht _) hP hq hS hs (weighted_chamber _ _) (weighted_chamber _ _))
      (zbO _))
    (mul_le_mul_of_nonneg_left (mix_le h h' h hP hq hS hs hp hP) (by positivity))
private theorem curve_nonneg (p q:Shape) (hq:bF q) (hp:bF p) :
    0≤ curve32 p p q p:= by
  unfold curve32
  exact add_nonneg (mul_nonneg (zbO _) (mix_nonneg p q p _ hq hp (weighted_chamber _ _)))
    (mul_nonneg (by positivity) (mix_nonneg p q p p hq hp hp))
private theorem num_le {p P q:Shape} (h:aO p P) (hp:bF p) (hP:bF P)
    (hq:bF q) (ht:p.t=1↔P.t=1) (k :ℕ) :
    pairNumerator false p p q (joinBody p q) k p.t ≤
      pairNumerator false P P q (joinBody P q) k P.t:= by
  have hj:aO (joinBody p q) (joinBody P q) :=
    ⟨max_le_max h.1 le_rfl,max_le_max h.2.1 le_rfl,max_le_max h.2.2 le_rfl⟩
  have hjp:=join_chamber hp hq
  have hjP:=join_chamber hP hq
  have hc:=curve_le hq hp hP hjp hjP h hj ht
  have hs :=curve_le hq hp hP hp hP h h ht
  have hs0:=curve_nonneg p q hq hp
  have hm:=mix_le h hj hj hP hq hjP hjp hjp hjP
  have hb: ((weightedChart (bf+1) p).b:ℤ)≤(weightedChart (bf+1) P).b :=
    Int.ofNat_le.mpr (weighted_mono h ht _).1
  have hpair :pair32 false p p q≤pair32 false P P q:= by
    change wP p q (weightedChart _ p) (weightedChart _ p) ≤
      wP P q (weightedChart _ P) (weightedChart _ P)
    exact mix_le h (weighted_mono h ht _) (weighted_mono h ht _) hP hq
      (weighted_chamber _ _) (weighted_chamber _ _) (weighted_chamber _ _) (weighted_chamber _ _)
  have hm' := mul_le_mul_of_nonneg_left hm (zbO mV)
  have hk0:=zbO k
  have hbc: (p.b:ℤ)≤P.b:=Int.ofNat_le.mpr h.1
  have hmax : ((max k p.t:ℕ) :ℤ)≤(max k P.t:ℕ) :=Int.ofNat_le.mpr (max_le_max_left k h.2.2)
  let d:ℤ:=mV
  let u:ℤ:=32*((P6.t:ℤ)+2*d)
  have hρ:=mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hbc (show 0≤u by positivity))
    (Int.natCast_nonneg q.b)
  have hcore :=add_le_add (mul_le_mul_of_nonneg_left hpair (zbO mV))
    (mul_le_mul hρ hb (zbO _) (show 0≤u*P.b*q.b by positivity))
  have hA:=mul_le_mul (mul_le_mul_of_nonneg_left hmax (by decide : (0:ℤ)≤2))
    hs hs0 (show 0≤(2 :ℤ)*(max k P.t:ℕ) by positivity)
  have hF:=mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_left hbc (show 0≤(64 :ℤ)*d*gZ by positivity))
    (zbO q.b)
  have hsum:=add_le_add hc hm'
  have haux :=add_le_add (add_le_add (add_le_add (add_le_add (mul_le_mul_of_nonneg_left hsum hk0) hs) hc) hA) hF
  have htotal:=add_le_add hcore haux
  by_cases hk :3≤k
  · simp only [pairNumerator,ite_eq_left hk]
    exact add_le_add (mul_le_mul_of_nonneg_right htotal (by omega :0≤(k :ℤ) - 2))
      (mul_le_mul_of_nonneg_left hsum hk0)
  · simp only [pairNumerator,ite_eq_right hk]
    exact add_le_add htotal (mul_le_mul_of_nonneg_left hc hk0)
theorem fee_mono {v r hi:Shape} {k :ℕ}
    (hr :3*r.t≤ r.j) (h:aO r hi) (ht:r.t=1↔hi.t=1) (hi' : 3*hi.t≤hi.j) :
    selfFee v r k false≤ selfFee v hi k false := by
  have hn:=num_le (On h) (Jg r hr)
    (Jg hi hi') (physical_chamber v k) ht k
  apply Nat.div_le_div_right
  exact zIu (zlr (Int.toNat_le_toNat hn) _) _
end q2w4Sxc
end
section
set_option autoImplicit true
namespace q2w4Sxc
open aR (Shape aO)
open P6_6 P6_6_8
open scoped BigOperators


abbrev used (v r :Shape) (k d:ℕ) :=
  (v.scale (d+1)).plus (r.scale (d+2 - k))
def layerMass (v r :Shape) (k d:ℕ) :ℕ:=pS (used v r k d)
abbrev mass (v r :Shape) (k n:ℕ) :=AJ.CL (layerMass v r k) n
private theorem used_mono (v r :Shape) (k :ℕ) {i j:ℕ} (h:i≤j) :
    aO (used v r k i) (used v r k j) := by
  have ha :=zlr h 1
  have hb:=zIu (zlr h 2) k
  exact ⟨z9f (ztf _ ha) (ztf _ hb),
    z9f (ztf _ ha) (ztf _ hb),
    z9f (ztf _ ha) (ztf _ hb)⟩
theorem layer_anti (v r :Shape) (k :ℕ) :Antitone (layerMass v r k) := by
  intro i j hij
  simpa only [layerMass,aUJ] using dNb (used_mono v r k hij)
abbrev massBlock (v r :Shape) (k start len:ℕ) :=
  AJ.CL (fun i=>layerMass v r k (start+i)) len
theorem massBlock_add (v r :Shape) (k start m n:ℕ) :
    massBlock v r k start (m+n) =
      massBlock v r k start m+massBlock v r k (start+m) n:= by
  simp only [AJ.bOw,Finset.sum_range_add,Nat.add_assoc]
theorem mass_eq_block (v r :Shape) (k n:ℕ) :mass v r k n=massBlock v r k 0 n:= by
  simp only [mass,massBlock,Nat.zero_add]
theorem companion_of_mass {v r :Shape} {k n:ℕ}
    (hz :layerMass v r k n=0) (hc:mass v r k n<gG) :CompanionTest v r k := by
  have hzero (d:ℕ) (hd:n≤d) :layerMass v r k d=0 :=
    Nat.eq_zero_of_le_zero ((layer_anti v r k hd).trans_eq hz)
  unfold CompanionTest
  simp only [← aUJ]
  change (∑ d∈Finset.range ack,layerMass v r k d)<gG
  rw [FI.aQD ack n hzero]
  change AJ.CL (layerMass v r k) n<gG at hc
  rw [AJ.bOw] at hc
  exact (Finset.sum_le_sum_of_subset (Finset.range_mono (min_le_right ack n))).trans_lt hc
end q2w4Sxc
end
