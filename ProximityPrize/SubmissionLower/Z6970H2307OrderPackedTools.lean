import ProximityPrize.SubmissionLower.Z6970H2307OrderPrefixChain

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 50000
set_option maxHeartbeats 0

namespace Height2307Orders


theorem prefixGood_append (r : K1_13.Shape) (a b : List PrefixEntry)
    (ha : prefixGood r a=true) (hb : prefixGood r b=true) :
    prefixGood r (a++b)=true := by
  simp only [prefixGood,List.all_append,Bool.and_eq_true] at *
  exact ⟨ha,hb⟩

structure VerifiedPrefix (r : K1_13.Shape) where
  entries : List PrefixEntry
  valid : prefixGood r entries = true

def joinPrefix (r : K1_13.Shape) (a b : VerifiedPrefix r) : VerifiedPrefix r :=
  ⟨a.entries ++ b.entries,prefixGood_append r a.entries b.entries a.valid b.valid⟩

theorem checkedVerified (r : K1_13.Shape) (map : VerifiedPrefix r) (ps : List Threshold)
    (h : ps.all (checkRow r map.entries)=true) : ps.all (checked r)=true :=
  checkedShard r map.entries ps map.valid h

def zeroPrefix (xs : List Threshold) : List PrefixEntry :=
  xs.map fun p => (p.stride,p.m-1,(p.m-1)*427286700047)

theorem zeroPrefix_good (xs : List Threshold) : prefixGood ⟨0,0,0⟩ (zeroPrefix xs)=true := by
  unfold prefixGood
  apply List.all_eq_true.mpr
  intro e he
  obtain ⟨p,_,rfl⟩ := List.mem_map.mp he
  exact decide_eq_true (beforeSlice_zero p.stride (p.m-1))

theorem all_take_drop {α : Type*} (f : α→Bool) (xs : List α) (n : ℕ)
    (ha : (xs.take n).all f=true) (hb : (xs.drop n).all f=true) :
    xs.all f=true := by
  rw [← List.take_append_drop n xs,List.all_append,ha,hb] <;> rfl

end Height2307Orders
