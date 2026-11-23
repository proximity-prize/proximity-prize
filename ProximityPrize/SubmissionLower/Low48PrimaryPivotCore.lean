import ProximityPrize.SubmissionLower.Low48PrimaryPivotRows

set_option Elab.async false
set_option maxHeartbeats 3000000
set_option maxRecDepth 10000

namespace Low48PrimaryPivot
open K1_13 (Geom)
open K1_13_1_1 (Form bandSpace backShift targetOrder)
open AnchorPivot82180 (E mon poly Term sound_monomial)
open AnchorPivot82180 (src0 src3 src6 src7 spec0 spec3 spec6 spec7)
open K1_13_2 K1_13_2_2 MvPolynomial
open scoped BigOperators
open private independent from ProximityPrize.SubmissionLower.AnchorPivotRank82180
open private active_range_le from ProximityPrize.SubmissionLower.Fast068

private def ofExp (e:JetExp):Triple:=⟨e 1,e 2,e 3⟩

private theorem old_jet_index (e : JetExp) :
    e.weight oldWeight=(ofExp e).index:=by
  simp [oldWeight,ofExp,Triple.index,Finsupp.weight_eq_sum,Fin.sum_univ_four,smul_eq_mul,mul_comm]

private theorem old_jet_degree (e : JetExp) :
    e.weight gradeWeight=e 0+e 1+e 2+e 3:=by
  simp [gradeWeight,Finsupp.weight_eq_sum,Fin.sum_univ_four]

private theorem source_data {i : BlockIndex} (hs : 1650 ≤ i.1.val)
    {e:JetExp} (he:e ∈ oldColumns (initialFlag i)) :
    (ofExp e).index ≤ 1650 ∧ -(offset i) ≤ ((ofExp e).index : ℤ) ∧
      e 0+e 1+e 2+e 3=1650:=by
  obtain ⟨hgrade,hlo,hhi,_⟩:=mem_oldColumns.mp he
  rw [old_jet_index] at hlo hhi
  rw [old_jet_degree] at hgrade
  have hg : (initialFlag i).degree = 1650 := by
    change min (i.1.val:ℤ) 1650=1650
    omega
  change ((ofExp e).index:ℤ)≤1650 at hhi
  rw [hg] at hgrade
  push_cast at hgrade
  exact ⟨by omega,hlo,by omega⟩

private theorem triple_injOn {i : BlockIndex} (hs : 1650 ≤ i.1.val) :
    Set.InjOn ofExp (↑(oldColumns (initialFlag i)):Set JetExp):=by
  intro e he f hf h
  have h1:=congrArg Triple.b h
  have h2:=congrArg Triple.c h
  have h3:=congrArg Triple.f h
  simp only [ofExp] at h1 h2 h3
  have hd:e 0+e 1+e 2+e 3=1650:=(source_data hs he).2.2
  have hdf:f 0+f 1+f 2+f 3=1650:=(source_data hs hf).2.2
  ext j
  fin_cases j
  · change e 0 = f 0
    omega
  · exact h1
  · exact h2
  · exact h3

private def good (i : BlockIndex) (e : JetExp) : Prop :=
  (initialFlag i).order.toNat≤(ofExp e).contact

private instance (i : BlockIndex) (e : JetExp) : Decidable (good i e) := by
  unfold good
  infer_instance

private theorem good_kernel {i : BlockIndex} (hs : 1650 ≤ i.1.val)
    (e : ↑((oldColumns (initialFlag i)).filter (good i))) :
    ∃ w : LinearMap.ker (flagContact (initialFlag i)),
      (encode (w.val:Form)).degree=(key (ofExp e).exponent:ℕ):=by
  obtain ⟨he,hg⟩:=Finset.mem_filter.mp e.property
  let p:=ofExp e
  obtain ⟨hi,hl,_⟩:=source_data hs he
  obtain ⟨hBand,hContact,hKey⟩:=row_sound p hi
  have hOld : polynomial p ∈ oldSpace (initialFlag i) := by
    intro e he
    have h:=(mem_restrictSupport_iff Geom).mp hBand he
    change K1_13_1_1.BandExponent 1650 p.index 1650 550 e at h
    obtain ⟨hd,hlow,hupp,ht⟩:=h
    refine ⟨?_,hl.trans hlow,hupp,?_⟩
    · have hweight : gradeWeight = (fun _ : Fin 4 => (1 : ℕ)) := rfl
      have hg : (initialFlag i).degree = 1650 := by
        change min (i.1.val:ℤ) 1650=1650
        omega
      rw [hweight, ← Finsupp.degree_eq_weight_one,hg]
      exact_mod_cast hd
    · change (e 3 : ℤ) ≤ 550
      exact_mod_cast ht
  let q:oldSpace (initialFlag i):=⟨polynomial p,hOld⟩
  have hz : q ∈ LinearMap.ker (flagContact (initialFlag i)) := by
    apply (weightedTruncation_eq_zero_iff _ _ _).mpr
    exact restrictWeightedOrder_anti _ hg hContact
  exact ⟨⟨q,hz⟩,hKey⟩

private theorem rank_le_bad (i : BlockIndex) (hs : 1650 ≤ i.1.val) :
    Module.finrank Geom (LinearMap.range (originBlock i)) ≤
      ((oldColumns (initialFlag i)).filter (fun e => ¬ good i e)).card:=by
  classical
  let S:=(oldColumns (initialFlag i)).filter (good i)
  let w : S → LinearMap.ker (flagContact (initialFlag i)) :=
    fun e => Classical.choose (good_kernel hs e)
  let L : LinearMap.ker (flagContact (initialFlag i)) →ₗ[Geom] Polynomial Geom :=
    encode.toLinearMap.comp ((oldSpace (initialFlag i)).subtype.comp (LinearMap.ker _).subtype)
  have keyInj : Function.Injective (fun e : S => key (ofExp e).exponent) := by
    intro p q hkey
    have hp:=(Finset.mem_filter.mp p.property).1
    have hq:=(Finset.mem_filter.mp q.property).1
    exact Subtype.ext (triple_injOn hs hp hq
      (key_injective _ _ (source_data hs hp).1 (source_data hs hq).1 hkey))
  have hind := independent L w (fun e => key (ofExp e).exponent) keyInj
    (fun e => Classical.choose_spec (good_kernel hs e))
  have hdim:=hind.fintype_card_le_finrank
  rw [Fintype.card_coe] at hdim
  have hnull:=(flagContact (initialFlag i)).finrank_range_add_finrank_ker
  rw [finrank_oldSpace] at hnull
  have hpartition := Finset.card_filter_add_card_filter_not
    (s:=oldColumns (initialFlag i)) (good i)
  have hbound:=(K1_13_2_2_1.proof i).trans (Submodule.finrank_mono (active_range_le i))
  change S.card≤_ at hdim
  change S.card+_=_ at hpartition
  omega

abbrev Column:=Fin 551 × Fin 826 × Fin 1651

def columnPoint (q:Column):Triple:=⟨q.2.2.val,q.2.1.val,q.1.val⟩

private def slot (p : Triple) (h : p.index ≤ 1650) : Column :=
  ⟨⟨p.f,by unfold Triple.index at h; omega⟩,
    ⟨p.c,by unfold Triple.index at h; omega⟩,
    ⟨p.b,by unfold Triple.index at h; omega⟩⟩

private theorem slot_inv (p : Triple) (h : p.index ≤ 1650) : columnPoint (slot p h) = p := by
  cases p
  rfl

def pays (i : BlockIndex) (q : Column) : Prop :=
  let p:=columnPoint q
  p.index≤1650 ∧ -offset i≤(p.index:ℤ) ∧ p.contact < (initialFlag i).order.toNat

instance (i : BlockIndex) (q : Column) : Decidable (pays i q) := by
  unfold pays
  infer_instance

def charge (i:BlockIndex) (q:Column):ℕ:=if pays i q then 1 else 0

set_option backward.isDefEq.respectTransparency false in
set_option maxRecDepth 26000 in
theorem block_le_charge (i : BlockIndex) (hs : 1650 ≤ i.1.val) :
    Module.finrank Geom (LinearMap.range (originBlock i)) ≤ ∑ q,charge i q:=by
  classical
  let f : JetExp → Column := fun e =>
    if hp:(ofExp e).index≤1650 then slot (ofExp e) hp else default
  let S:Finset JetExp:=(oldColumns (initialFlag i)).filter (fun e => ¬ good i e)
  let T:Finset (Column):=Finset.univ.filter (pays i)
  have hT : (∑ q, charge i q) = T.card := by
    unfold charge T
    rw [Finset.sum_boole]
    rfl
  rw [hT]
  refine (rank_le_bad i hs).trans (Finset.card_le_card_of_injOn (s:=S) (t:=T) f ?_ ?_)
  · intro e he
    have helem:e ∈ (oldColumns (initialFlag i)).filter (fun e => ¬ good i e):=he
    obtain ⟨hm,hbad⟩:=Finset.mem_filter.mp helem
    obtain ⟨hi,hl,_⟩:=source_data hs hm
    unfold f
    rw [dite_eq_left hi]
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_univ _,?_⟩
    unfold pays
    rw [slot_inv]
    exact ⟨hi,hl,lt_of_not_ge hbad⟩
  · intro e he q hq h
    have hem := (Finset.mem_filter.mp
      (show e ∈ (oldColumns (initialFlag i)).filter (fun e => ¬ good i e) from he)).1
    have hqm := (Finset.mem_filter.mp
      (show q ∈ (oldColumns (initialFlag i)).filter (fun e => ¬ good i e) from hq)).1
    have hei:=(source_data hs hem).1
    have hqi:=(source_data hs hqm).1
    simp only [f,dite_eq_left hei,dite_eq_left hqi] at h
    have heq:=congrArg columnPoint h
    rw [slot_inv,slot_inv] at heq
    exact triple_injOn hs hem hqm heq

#print axioms block_le_charge

end Low48PrimaryPivot
