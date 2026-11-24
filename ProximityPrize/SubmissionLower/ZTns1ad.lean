import ProximityPrize.SubmissionLower.ZLcmX9d
import Mathlib.LinearAlgebra.LinearIndependent.BaseChange
import ProximityPrize.SubmissionLower.ZV1UoEe
import ProximityPrize.SubmissionLower.Zn6yRJc
import ProximityPrize.SubmissionLower.ZzOuVbd
import ProximityPrize.SubmissionLower.ZxJP4ta
import ProximityPrize.SubmissionLower.ZAW6pTc
set_option Elab.async false
open _root_ renaming Fintype.card → zhP, LinearIndependent → z14, LinearMap.range → zWl, Matrix.det_diagonal → zCi, Matrix.rank_eq_finrank_span_cols → z0e, Module.finrank → zsE, Module.finrank_fintype_fun_eq_card → zvt
set_option maxHeartbeats 4000000
section
set_option autoImplicit true
namespace qBo7Whe
private def packed :Array (ℕ×ℕ×ℕ) := #[
  (52,5,0x6090c10101),(57,0,0x4),(57,0,0x4),(57,0,0x5),
  (51,6,0x446090c10101),(56,1,0x504),(56,1,0x504),(56,1,0x605),
  (50,7,0x30446090c10101),(55,2,0x48504),(55,2,0x48504),(55,2,0x54605),
  (49,8,0x2130446090c10101),(54,3,0x3848504),(54,3,0x3848504),(54,3,0x4054605),
  (48,9,0x162130446090c10101),(53,4,0x283848504),(53,4,0x283848504),(53,4,0x2d4054605),
  (47,10,0xe562130446090c10101),(52,5,0x1b283848504),(52,5,0x1b283848504),(52,5,0x1e2d4054605),
  (46,11,0x8ce562130446090c10101),(51,6,0x111c283848504),(51,6,0x105ba83848504),(51,6,0x11df304054605),
  (45,12,0x5092f562130446090c10101),(50,7,0x9719dab3848504),(50,7,0x9319e2e3848504),(50,7,0x972a1354654605),
  (44,12,0x559f0d9a130446090c10101),(49,7,0x9f361333e48504),(49,6,0x1361b54648504),(49,6,0x13a5be5a60605),
  (43,11,0xb531e2830446090c10101),(48,6,0x1466bd5454504),(48,5,0x29415e64504),(48,5,0x284b708c785),
  (42,10,0x17e5b63e446090c10101),(47,5,0x294d6e80684),(47,4,0x5680a0884),(47,4,0x529ad0d08),
  (41,9,0x30495c606090c10101),(46,4,0x55a0d0c07),(46,3,0xacfd08b),(45,4,0x549ec4a03),
  (40,8,0x6194a49890c10101),(44,4,0x55a0c4a03),(44,3,0xb104f08),(43,4,0x539cbc904),
  (39,7,0xc52d4120c10101),(42,4,0x55a0c4a05),(41,4,0x57807c581),(40,5,0x2a4f625c381),
  (38,6,0x1824ab2618101),(39,5,0x2ad06868482),(38,5,0x2abe4c40201),(37,6,0x1527b83c30201),
  (37,5,0x2f48605c403),(36,6,0x146639443c302),(35,6,0x1561ae2e24201),(34,7,0xa941f282624201),
  (34,6,0x1563b43a34302),(33,7,0xa33dfac2e30302),(32,7,0xa319aa02024201),(31,7,0xa71599d2024201),
  (31,7,0x9715ba52830302),(30,7,0xa315aa12830302),(29,8,0x4c94f56192024201),(28,8,0x4d8ce53992024201),
  (28,7,0x90f981e2830302),(27,8,0x4d94f969e2830302),(26,8,0x4682d52192024201),(25,8,0x4a84d12192024201),
  (25,7,0x86e551e2830302),(24,7,0x8ce951e2830302),(23,7,0x7cc52192024201),(22,7,0x80c52192024201),
  (22,6,0xe151e2830302),(21,6,0xe151e2830302),(20,6,0xc52192024201),(19,6,0xc52192024201),
  (19,5,0x151e2830302),(18,5,0x151e2830302),(17,5,0x12192024201),(16,5,0x12192024201),
  (16,4,0x1e2830302),(15,4,0x1e2830302),(14,4,0x192024201),(13,4,0x192024201),
  (13,3,0x2830302),(12,3,0x2830302),(11,3,0x2024201),(10,3,0x2024201),
  (10,2,0x30302),(9,2,0x30302),(8,2,0x24201)]
def below (g k :ℕ) :ℕ :=
  let (start,len,z) :=packed[g]?.getD (0,0,0)
  let k :=min k 57
  if k<start then 0 else (z >>> (7*min (k - start) len)) % 128
end qBo7Whe
end
section
set_option autoImplicit true
namespace qBo7Whe
open qK9H6va (offset)
open qxuyiwe (Pivot PivotIndex FF profileCutoff h51)
open fP (qI Qg)
private theorem hist_length:h51.length=99:=rfl
private theorem checked_gap_at (g:ℕ) (hg:g<99) :
    below g 57=h51[g]! ∧
    (List.range 57).all (fun k=>decide (below g k≤below g (k+1)))=true := by
  have h:(List.range 99).all (fun g=>decide (below g 57=h51[g]!) &&
      (List.range 57).all (fun k=>decide (below g k≤below g (k+1))))=true := by decide +kernel
  have h2:=List.all_eq_true.mp h g (List.mem_range.mpr hg)
  rw [Bool.and_eq_true,decide_eq_true_eq] at h2
  exact h2
private theorem checked_gap (g:Fin h51.length) :
    below g 57=h51[g.val] ∧
    (List.range 57).all (fun k=>decide (below g k≤below g (k+1)))=true := by
  have h:=checked_gap_at g (hist_length ▸ g.isLt)
  simpa only [getElem!_pos h51 g.val g.isLt] using h
private theorem below_clamp (g k :ℕ) (hk :57≤k) :below g k=below g 57:= by
  unfold below
  rw [min_eq_right hk]
  rfl
private theorem below_mono (g:Fin h51.length) :Monotone (below g) := by
  apply monotone_nat_of_le_succ
  intro k
  by_cases hk :k<57
  · exact of_decide_eq_true (List.all_eq_true.mp (checked_gap g).2 k (List.mem_range.mpr hk))
  · rw [below_clamp _ _ (by omega),below_clamp _ (k+1) (by omega)]
private theorem slot_lt_last (j:Pivot h51) :j.2.val<below j.1 (56+1) := by
  rw [show 56+1=57 by rfl,(checked_gap j.1).1]
  exact j.2.isLt
private theorem hasIndex (j:Pivot h51) : ∃ i,j.2.val<below j.1 (i+1) :=
  ⟨56,slot_lt_last j⟩
def ix51 :PivotIndex h51 := fun j =>
  ⟨Nat.find (hasIndex j),Nat.lt_succ_of_le <| Nat.find_min' (hasIndex j) (slot_lt_last j)⟩
private def slots (r g:ℕ) :ℕ:=below g (155 - r - g) - below g (56 - r)
def gH (r :ℕ) :ℕ:=qI 99 (slots r)
private def payingSlot (r :ℕ)
    (a :Σ g:Fin h51.length,Fin (slots r g)) :
    FF ix51 (offset r) (profileCutoff 51 51 (offset r)) := by
  let lo:=56 - r
  let hi:=155 - r-a.1.val
  let k :=below a.1 lo+a.2.val
  have hs :a.2.val<below a.1 hi - below a.1 lo:=a.2.isLt
  have hk :k<below a.1 hi:= by dsimp [k]; omega
  have hi' : hi≤57∨57≤hi:=le_total _ _
  have hbound:below a.1 hi≤below a.1 57:= by
    rcases hi' with h | h
    · exact below_mono a.1 h
    · exact (below_clamp _ _ h).le
  let j:Pivot h51 :=⟨a.1,⟨k,hk.trans_le (hbound.trans_eq (checked_gap a.1).1)⟩⟩
  have hhi: (ix51 j).val<hi:= by
    have hn:lo<hi:= by
      by_contra! h
      have hh:=below_mono a.1 h
      omega
    have hm:j.2.val<below j.1 (hi - 1+1) := by
      rw [show hi - 1+1=hi by omega]
      exact hk
    have hf :=Nat.find_min' (hasIndex j) hm
    change Nat.find (hasIndex j)<hi
    omega
  have hlo:lo≤(ix51 j).val := by
    have hf :j.2.val<below j.1 ((ix51 j).val+1) :=Nat.find_spec (hasIndex j)
    by_contra! h
    have hb:below j.1 ((ix51 j).val+1)≤below j.1 lo:=below_mono a.1 (by omega)
    change k<below a.1 ((ix51 j).val+1) at hf
    change below a.1 ((ix51 j).val+1)≤below a.1 lo at hb
    dsimp [k] at hf
    omega
  refine ⟨j,?_,?_⟩
  · unfold profileCutoff qK9H6va.Vm offset
    change (a.1.val :ℤ)+(ix51 j).val<99 - 51-((r :ℤ) - 56)+51
    dsimp [hi] at hhi
    omega
  · unfold offset
    dsimp [lo] at hlo
    omega
theorem paid_le_eligible (r :ℕ) :
    gH r≤zhP (FF ix51 (offset r) (profileCutoff 51 51 (offset r))) := by
  classical
  have hinj:Function.Injective (payingSlot r) := by
    rintro ⟨g,i⟩ ⟨h,j⟩ he
    have hh:g=h:=congrArg (fun p=>p.val.1) he
    subst h
    have hk :below g (56 - r)+i.val=below g (56 - r)+j.val :=
      congrArg (fun p=>p.val.2.val) he
    have hj:i=j:=Fin.ext (Nat.add_left_cancel hk)
    subst j
    rfl
  calc
    gH r=zhP (Σ g:Fin h51.length,Fin (slots r g)) := by
      rw [gH,Fintype.card_sigma]
      simp only [Fintype.card_fin]
      simpa only [hist_length] using Qg h51.length (slots r)
    _≤_:=Fintype.card_le_of_injective _ hinj
end qBo7Whe
end
section
set_option autoImplicit true
namespace qBo7Whe
open aR (ao)
open fP (GS Jx avQ avP)
open xE (Flag)
open akL (ahV KP BU aDd)
open qK9H6va
open P6_6_2 (oppositeBound latticeAllowance)
open qnnEPee
open MvPolynomial
open private bpX from ProximityPrize.SubmissionLower.ZLIH4nd
open private dgL from ProximityPrize.SubmissionLower.ZV1UoEe
open private ker_embed tail_card rank_le_of_ker_le from ProximityPrize.SubmissionLower.ZUihISc
noncomputable section
local instance :Fact (Nat.Prime P1.p) :=⟨KoalaBear.is_prime⟩
private instance :CharP ao P1.p :=
  charP_of_injective_algebraMap (algebraMap K1.K ao).injective P1.p
private abbrev Ground :=ZMod P1.p
private def castField:Ground →+* ao:=ZMod.castHom (dvd_refl P1.p) ao
private theorem base_rank_le {m n:Type} [Fintype m] [Fintype n] (A:Matrix m n Ground) :
    A.rank≤(A.map castField).rank := by
  classical
  let:Algebra Ground ao:=castField.toAlgebra
  rw [z0e,z0e]
  let V:=Submodule.span Ground (Set.range A.col)
  let W:=Submodule.span ao (Set.range (A.map castField).col)
  let b:=Module.finBasis Ground V
  let f :=Pi.algebraMap m Ground ao
  have hmap {x :m→Ground} (hx :x∈V) :f x∈W:= by
    induction hx using Submodule.span_induction with
    | mem x hx =>
        obtain ⟨j,rfl⟩:=hx
        exact Submodule.subset_span (Set.mem_range_self j)
    | zero=>simpa only [map_zero] using W.zero_mem
    | add x y _ _ hx hy=>simpa only [map_add] using W.add_mem hx hy
    | smul a x _ hx =>
        have h:f (a•x)=(algebraMap Ground ao a)•f x := by
          ext i
          simp [f,Pi.algebraMap,Algebra.smul_def]
        rw [h]
        exact W.smul_mem _ hx
  let v (i:Fin (zsE Ground V)) :W :=
    ⟨f (b i).val,hmap (b i).property⟩
  have hi:z14 ao (fun i=>f (b i).val) :=
    (linearIndependent_algebraMap_comp_iff (R:=Ground) (S:=ao)).mpr
      (b.linearIndependent.map' V.subtype V.ker_subtype)
  have hv :z14 ao v :=LinearIndependent.of_comp W.subtype hi
  simpa only [Fintype.card_fin] using hv.fintype_card_le_finrank
private theorem rank_pascal_le_block (q:ℕ) (g:ℤ) :
    (Gy q g).rank≤zsE ao (zWl (auo q g)) := by
  classical
  let VY:=(dgL q g).comp (auo q g)
  let basis :Module.Basis (XN q g) ao (GS (iO q) (-g) 56 16) :=
    basisRestrictSupport ao _
  let E :Matrix (ait q g) (XN q g) ao :=
    Matrix.of fun e m=>VY (basis m) e
  let M:=(Gy q g).map castField
  let R:=Matrix.diagonal fun e :ait q g=>avQ e.val
  let C:=Matrix.diagonal fun m:XN q g=>avP m.val
  have hd:iO q≤56:=(min_le_right _ _).trans (gAv q)
  have hE :E=R*M*C:= by
    ext e m
    rw [Matrix.mul_diagonal,Matrix.diagonal_mul]
    change (auo q g (basis m)).coeff e.val =
      avQ e.val*castField (Gy q g e m)*avP m.val
    have hm: (basis m:fP.Form)=monomial m.val 1 :=
      coe_basisRestrictSupport_apply (R:=ao) _ m
    change (weightedTruncation fP.m9 (Vm q g).toNat
      (Jx (basis m))).coeff e.val= _
    rw [coeff_weightedTruncation,ite_eq_left e.property.2,hm]
    rw [c3K _ _ (m.property.1.trans e.property.1.symm) (m.property.1.trans_le hd)]
    simp only [Gy,prefixMatrix,map_mul,map_natCast]
    ac_rfl
  have hR:R.det≠0:= by
    rw [zCi]
    exact Finset.prod_ne_zero_iff.mpr fun e _ =>
      div_ne_zero (pow_ne_zero _ (neg_ne_zero.mpr one_ne_zero))
        (bpX _ (e.property.1.trans_le hd))
  have hC:C.det≠0:= by
    rw [zCi]
    exact Finset.prod_ne_zero_iff.mpr fun m _ =>
      mul_ne_zero (pow_ne_zero _ (neg_ne_zero.mpr one_ne_zero))
        (bpX _ (m.property.1.trans_le hd))
  calc
    _≤M.rank :=base_rank_le _
    _=E.rank := by rw [hE,Matrix.rank_mul_eq_left_of_det_ne_zero _ _ hC,
      Matrix.rank_mul_eq_right_of_det_ne_zero _ _ hR]
    _=zsE ao (zWl VY) :=Matrix.rank_of_basis basis VY
    _≤_:= by
      rw [show VY=(dgL q g).comp (auo q g) by rfl,LinearMap.range_comp]
      let:Module.Finite ao (GS (iO q) (-g) 56 16) :=
        Module.Finite.of_basis basis
      exact Submodule.finrank_map_le _ _
def flag (q:ℕ) (g:ℤ) :Flag:=⟨iO q,-g,56,16,Vm q g⟩
private theorem rank_le_flag (q:ℕ) (g:ℤ) :
    (Gy q g).rank≤zsE ao (zWl (KP (flag q g))) := by
  have hs :GS (iO q) (-g) 56 16≤ahV (flag q g) := by
    intro Q hQ e he
    obtain ⟨hd,hlo,hhi,hf⟩:=hQ he
    change (e.weight BU:ℤ)=(iO q:ℤ) ∧
      (-g)≤(e.weight akL.Oq:ℤ) ∧
      (e.weight akL.Oq:ℤ)≤56∧(e 3:ℤ)≤16
    refine ⟨?_,hlo,hhi,by exact_mod_cast hf⟩
    change (e.weight (fun _:Fin 4=>(1 :ℕ)) :ℤ)=(iO q:ℤ)
    rw [← Finsupp.degree_eq_weight_one]
    exact_mod_cast hd
  have h:auo q g=(KP (flag q g)).comp (Submodule.inclusion hs) := by
    ext x
    rfl
  exact (rank_pascal_le_block q g).trans (by
    rw [h]
    exact Submodule.finrank_mono (LinearMap.range_comp_le_range _ _))
open xE (oldCount U1)
private theorem positive_flag_bound (F:Flag) (ho:0<F.order) (hl:0<F.lower)
    (hguard :F.lower≤1710) :
    zsE ao (zWl (KP F))≤oppositeBound F:= by
  have hker :=ker_embed F
  have hn:=(KP F).finrank_range_add_finrank_ker
  rw [aDd] at hn
  have hc:=bjv.proof aw7.proof F
  have hd:=(debitMap F).finrank_range_add_finrank_ker
  rw [zvt,Fintype.card_coe] at hd
  have ht:=tail_card F
  let belowRows :=U1 F.degree (min F.upper (F.order - 1)) F.cap
  let tail:=U1 F.degree F.upper F.cap - belowRows
  change ((tailColumns F).card:ℤ)=tail at ht
  let D:=zsE ao (zWl (debitMap F))
  have h₀:D ≤(reducedColumns F).card:= calc
    _≤zsE ao (zWl (momentMap F (momentColumns F))) :=
      rank_le_of_ker_le (qajFMeb.proof F hl hguard)
    _≤zsE ao (zWl (momentMap F (reducedColumns F))) :=
      rank_le_of_ker_le (qO9urca.proof F ho hl)
    _≤_:= by
      simpa only [zvt,Fintype.card_coe] using
        Submodule.finrank_le (zWl (momentMap F (reducedColumns F)))
  have h₁: (D:ℤ)≤latticeAllowance F:= by rw [← reduced_card F]; exact_mod_cast h₀
  have h₂: (D:ℤ)≤tail:= by
    rw [← ht]
    dsimp [D]
    omega
  have hm:=le_min h₁ h₂
  unfold oppositeBound
  rw [ite_eq_right (not_le_of_gt ho),ite_eq_right (not_le_of_gt hl)]
  change _≤(oldCount F - tail+min (latticeAllowance F) tail).toNat
  dsimp [D] at hm
  omega
theorem rank_le_opposite (q:ℕ) (g:ℤ) (ho:0<Vm q g)
    (hl:0 < -g) (hu : -g≤1710) :
    (Gy q g).rank≤oppositeBound (flag q g) :=
  (rank_le_flag q g).trans (positive_flag_bound _ ho hl hu)
end
end qBo7Whe
end
section
set_option autoImplicit true
namespace qBo7Whe
open qK9H6va
open q1jcGec (a2M bve fTf fTk)
open qxuyiwe (profileCutoff)
private theorem ay9 (q:ℕ) (hq:iO q=51) :q=51 := by
  unfold iO P6_6_1.asu at hq
  by_cases h₁:q≤111
  · rw [ite_eq_left h₁,min_eq_left (show q≤56 by
      by_contra! h
      rw [min_eq_right h.le] at hq
      omega)] at hq
    exact hq
  rw [ite_eq_right h₁] at hq
  by_cases h₂:q≤129
  · rw [ite_eq_left h₂,min_eq_right (by omega)] at hq
    omega
  · rw [ite_eq_right h₂,min_eq_right (by omega)] at hq
    omega
private def cap (r :ℕ) :ℕ :=
  if r<48 then a2M 51 (56 - r)
  else if r≤49 then P6_6_2.oppositeBound (flag 51 (offset r))
  else bve 51 (104 - r)
private theorem rank_le_cap (r :ℕ) (hr :r<104) :
    (Gy 51 (offset r)).rank≤ cap r := by
  unfold cap
  by_cases hc:r<48
  · rw [ite_eq_left hc]
    exact fTf 51 r
  rw [ite_eq_right hc]
  by_cases hf :r≤49
  · rw [ite_eq_left hf]
    apply rank_le_opposite <;> simp only [Vm,offset] <;> omega
  rw [ite_eq_right hf]
  have he : (Vm 51 (offset r)).toNat=104 - r := by
    unfold offset Vm
    omega
  rw [← he]
  exact fTk 51 (offset r)
private def counts :Array ℕ := #[
    276,546,810,1067,1317,1559,1793,2018,2235,2443,2643,2835, 3019,
    3195, 3364,3525, 3679,3826,3966,4099,4226,4346,4460,4568,4670,4766,
    4857,4942,5022,5097,5167,5232,5293,5349,5401,5449,5493,5533,5570,
    5603,5633,5660,5684,5705, 5724,5740,5754,5766,5520,5260,4997,4740,
    4490,4248,4014,3789,3572,3364,3164, 2972,2788,2612,2443,2282,2128,
    1981,1841,1708,1581,1461,1347,1239,1137,1041,950,865,785,710,
    640,575, 514,458,406,358,314, 274, 237,204,174,147,123,
    102,83,67,53,41,31, 23,16,11,7,4, 2,1]
private theorem checked (r :ℕ) (hc:cap r=counts[r]?.getD 0)
    (hp:gH r=counts[r]?.getD 0) :cap r≤gH r :=
  (hc.trans hp.symm).le
private theorem checked_caps (r :ℕ) (hr :r<104) :cap r≤gH r := by
  have h:(List.range 104).all (fun r=>decide (cap r≤gH r))=true := by decide +kernel
  exact of_decide_eq_true (List.all_eq_true.mp h r (List.mem_range.mpr hr))
theorem proof :qxuyiwe.c1 := by
  refine ⟨ix51,?_⟩
  intro q hq r
  have h:=ay9 q hq
  subst q
  change (Gy 51 (offset r)).rank ≤
    zhP (qxuyiwe.FF ix51 (offset r) (profileCutoff 51 51 (offset r)))
  by_cases hr :r.val<104
  · exact ((rank_le_cap r hr).trans (checked_caps r hr)).trans (paid_le_eligible r)
  · rw [qaTCFjd.rank_eq_zero 51 r (by omega)]
    exact Nat.zero_le _
end qBo7Whe
end
