import ProximityPrize.SubmissionLower.Final50Price

open scoped BigOperators

set_option Elab.async false
set_option maxHeartbeats 2000000
set_option maxRecDepth 16000
namespace Final50FatReserve
open K1_13 (Shape chart ceilDiv mixed32)
open K1_13_8 (Valid)
open K1_13_8_4 (TotalLE IndexFits mixed_mono_total)
open Final50Price (fatPrice linearChart taylorLength physicalDegree incidenceGap
  resultantBox commonBox fatOrder divisorOrder isolatedOrder)

/-- Degree cap at each index of the retained product. -/
def degreeCap : ℕ → ℕ
  | 3 => 26
  | 4 => 24
  | 5 => 21
  | 6 => 17
  | 7 => 12
  | 8 => 3
  | _ => 0

def charge (b j t : ℕ) : ℕ :=
  match t, j with
  | 1, 3 =>
    if b ≤ 3 then 2439983170614103
    else if b ≤ 4 then 2887537493876781
    else if b ≤ 5 then 3342399058454941
    else if b ≤ 6 then 3806706566388700
    else if b ≤ 7 then 4282598719718179
    else if b ≤ 8 then 4772214220483498
    else if b ≤ 9 then 5277691770724777
    else if b ≤ 10 then 5801170072482136
    else if b ≤ 11 then 6344787827795695
    else if b ≤ 12 then 6910683738705574
    else if b ≤ 13 then 7500996507251894
    else if b ≤ 14 then 8117864835474772
    else if b ≤ 15 then 8763427425414332
    else if b ≤ 16 then 9439822979110691
    else if b ≤ 17 then 10149190198603970
    else if b ≤ 18 then 10893667785934288
    else if b ≤ 19 then 11675394443141768
    else if b ≤ 20 then 12496508872266526
    else if b ≤ 21 then 13359149775348686
    else if b ≤ 22 then 14265455854428365
    else if b ≤ 23 then 15217565811545685
    else if b ≤ 24 then 16217618348740763
    else if b ≤ 25 then 17267752168053723
    else 18370105971524682
  | 1, 4 =>
    if b ≤ 4 then 6299561324843083
    else if b ≤ 5 then 7433544753833797
    else if b ≤ 6 then 8576974126180111
    else if b ≤ 7 then 9731988143922146
    else if b ≤ 8 then 10900725509100020
    else if b ≤ 9 then 12085324923753854
    else if b ≤ 10 then 13287925089923768
    else if b ≤ 11 then 14510664709649883
    else if b ≤ 12 then 15755682484972317
    else if b ≤ 13 then 17025117117931191
    else if b ≤ 14 then 18321107310566625
    else if b ≤ 15 then 19645791764918740
    else if b ≤ 16 then 21001309183027654
    else if b ≤ 17 then 22389798266933488
    else if b ≤ 18 then 23813397718676362
    else if b ≤ 19 then 25274246240296396
    else if b ≤ 20 then 26774482533833711
    else if b ≤ 21 then 28316245301328425
    else if b ≤ 22 then 29901673244820659
    else if b ≤ 23 then 31532905066350533
    else 33212079467958168
  | 1, 5 =>
    if b ≤ 5 then 13960112930406532
    else if b ≤ 6 then 16086403277091932
    else if b ≤ 7 then 18224278269173051
    else if b ≤ 8 then 20375876608690010
    else if b ≤ 9 then 22543336997682930
    else if b ≤ 10 then 24728798138191929
    else if b ≤ 11 then 26934398732257128
    else if b ≤ 12 then 29162277481918648
    else if b ≤ 13 then 31414573089216607
    else if b ≤ 14 then 33693424256191126
    else if b ≤ 15 then 36000969684882326
    else if b ≤ 16 then 38339348077330325
    else if b ≤ 17 then 40710698135575244
    else if b ≤ 18 then 43117158561657204
    else if b ≤ 19 then 45560868057616323
    else if b ≤ 20 then 48043965325492722
    else 50568589067326522
  | 1, 6 =>
    if b ≤ 6 then 24658237049155780
    else if b ≤ 7 then 27707324685861334
    else if b ≤ 8 then 30770135670002727
    else if b ≤ 9 then 33848808703620082
    else if b ≤ 10 then 36945482488753514
    else if b ≤ 11 then 40062295727443148
    else if b ≤ 12 then 43201387121729102
    else if b ≤ 13 then 46364895373651496
    else if b ≤ 14 then 49554959185250448
    else if b ≤ 15 then 52773717258566083
    else if b ≤ 16 then 56023308295638516
    else 59305870998507870
  | 1, 7 =>
    if b ≤ 7 then 38544290629529057
    else if b ≤ 8 then 42518314258294884
    else if b ≤ 9 then 46508199936536673
    else if b ≤ 10 then 50516086366294540
    else if b ≤ 11 then 54544112249608608
    else 58594416288518996
  | 2, 6 =>
    if b ≤ 2 then 81714165064113322
    else if b ≤ 3 then 81714165064113332
    else if b ≤ 4 then 81714165064113346
    else if b ≤ 5 then 81714165064113364
    else if b ≤ 6 then 81714165064113386
    else if b ≤ 7 then 93284943258622565
    else if b ≤ 8 then 104910261631318549
    else if b ≤ 9 then 116598675503013336
    else if b ≤ 10 then 128358740194518928
    else if b ≤ 11 then 140199011026647323
    else if b ≤ 12 then 152098002828027510
    else if b ≤ 13 then 164060350654950048
    else if b ≤ 14 then 176128570584931389
    else if b ≤ 15 then 188311217938783535
    else if b ≤ 16 then 200616848037318485
    else 213054016201348239
  | 2, 7 =>
    if b ≤ 3 then 148332074221376742
    else if b ≤ 4 then 148332074221376756
    else if b ≤ 5 then 148332074221376774
    else if b ≤ 6 then 148332074221376796
    else if b ≤ 7 then 148332074221376822
    else if b ≤ 8 then 165800593934781044
    else if b ≤ 9 then 183316222130448544
    else if b ≤ 10 then 200903501145926849
    else if b ≤ 11 then 218570986302027958
    else 236327232919563871
  | 1, 8 =>
    55620412373566483
  | 2, 8 =>
    210450798522107942
  | _, _ => 0

private theorem check_single : ∀ (b : Fin 27) (j : Fin 9) (t : Fin 3),
    Valid (⟨b.val,j.val,t.val⟩ : Shape) → b.val ≤ degreeCap j.val →
      fatPrice ⟨b.val,j.val,t.val⟩≤charge b.val j.val t.val:=by decide +kernel

theorem single (x : Shape) (hv : Valid x) (hj : x.j ≤ 8) (hb : x.b ≤ degreeCap x.j) :
    fatPrice x≤charge x.b x.j x.t:=by
  obtain ⟨b,j,t⟩:=x
  change j≤8 at hj
  change b≤degreeCap j at hb
  have hpos : 1 ≤ t := hv.1
  have hindex : 3 * t ≤ j := hv.2.1
  have hj0 : 3 ≤ j := by omega
  have ht : t < 3 := by omega
  have hb0:b < 27:=by interval_cases j <;> simp [degreeCap] at hb <;> omega
  exact check_single ⟨b,hb0⟩ ⟨j,by omega⟩ ⟨t,ht⟩ hv hb

private theorem check_pair (j k : ℕ)
    (h:(j=3 ∧ k=3) ∨ (j=3 ∧ k=4) ∨ (j=4 ∧ k=3)) :
    ∀ b c : Fin 18, j ≤ 3*b.val → k ≤ 3*c.val → b.val+c.val ≤ degreeCap (j+k) →
      fatPrice ⟨b.val,j,1⟩+fatPrice ⟨c.val,k,1⟩≤charge (b.val+c.val) (j+k) 2:=by
  rcases h with ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩ <;> decide +kernel

private theorem check_pair_eight :
    ∀ (b c : Fin 4) (j k : Fin 6), 3 ≤ j.val → 3 ≤ k.val → j.val+k.val=8 →
      j.val≤3*b.val→k.val≤3*c.val→b.val+c.val≤3 →
      fatPrice ⟨b.val,j.val,1⟩+fatPrice ⟨c.val,k.val,1⟩≤charge (b.val+c.val) 8 2:=by
  decide +kernel

theorem pair (b c j k : ℕ) (hj : 3 ≤ j) (hk : 3 ≤ k) (hjk : j + k ≤ 8)
    (hb:j≤3*b) (hc:k≤3*c) (hbc:b+c≤degreeCap (j+k)) :
    fatPrice ⟨b,j,1⟩+fatPrice ⟨c,k,1⟩≤charge (b+c) (j+k) 2:=by
  by_cases he:j+k=8
  · have hbc' : b+c ≤ 3 := by simpa [he,degreeCap] using hbc
    rw [he]
    exact check_pair_eight ⟨b,by omega⟩ ⟨c,by omega⟩ ⟨j,by omega⟩ ⟨k,by omega⟩
      hj hk he hb hc hbc'
  · have h : (j = 3 ∧ k = 3) ∨ (j = 3 ∧ k = 4) ∨ (j = 4 ∧ k = 3) := by omega
    have hsum : b+c ≤ 17 := by
      have h' : j+k=6 ∨ j+k=7:=by omega
      rcases h' with h' | h' <;> simp only [h', degreeCap] at hbc <;> omega
    exact check_pair j k h ⟨b,by omega⟩ ⟨c,by omega⟩ hb hc hbc

/-- Reserve for the whole family of retained factors. -/
theorem family (n : ℕ) (a : Fin n → Shape) (hv : ∀ i, Valid (a i))
    (hj:(∑ i,(a i).j)≤8)
    (hb:(∑ i,(a i).b)≤degreeCap (∑ i,(a i).j)) :
    (∑ i,fatPrice (a i))≤charge (∑ i,(a i).b) (∑ i,(a i).j) (∑ i,(a i).t):=by
  have hsum : 3 * (∑ i, (a i).t) ≤ ∑ i, (a i).j := by
    rw [Finset.mul_sum]
    exact Finset.sum_le_sum fun i _ => (hv i).2.1
  have hn' : n ≤ ∑ i, (a i).t := calc
    n = ∑ _:Fin n,1:=by simp
    _ ≤ ∑ i,(a i).t:=Finset.sum_le_sum fun i _ => (hv i).1
  have hn:n≤2:=by omega
  interval_cases n
  · simp [charge]
  · simp only [Fin.sum_univ_one] at hj hb ⊢
    exact single _ (hv 0) hj hb
  · simp only [Fin.sum_univ_two] at hsum hj hb ⊢
    have ht0:=(hv 0).1
    have ht1:=(hv 1).1
    have h0:(a 0).t=1:=by omega
    have h1:(a 1).t=1:=by omega
    have he (i:Fin 2):a i=⟨(a i).b,(a i).j,(a i).t⟩:=by cases a i; rfl
    have hh := pair (a 0).b (a 1).b (a 0).j (a 1).j
      (by simpa only [h0] using (hv 0).2.1) (by simpa only [h1] using (hv 1).2.1)
      hj (hv 0).2.2 (hv 1).2.2 hb
    have ha0 : a 0 = ⟨(a 0).b, (a 0).j, 1⟩ :=
      (he 0).trans (congrArg (fun t => (⟨(a 0).b,(a 0).j,t⟩:Shape)) h0)
    have ha1 : a 1 = ⟨(a 1).b, (a 1).j, 1⟩ :=
      (he 1).trans (congrArg (fun t => (⟨(a 1).b,(a 1).j,t⟩:Shape)) h1)
    rw [h0,h1]
    simpa only [← ha0, ← ha1] using hh

#print axioms single
#print axioms pair
#print axioms family
end Final50FatReserve
