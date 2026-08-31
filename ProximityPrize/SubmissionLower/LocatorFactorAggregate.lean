import ProximityPrize.Benchmark.TargetLower
import ProximityPrize.SubmissionLower.D
namespace ProximityPrize.SubmissionLower.LocatorFactorAggregate
open scoped BigOperators
open RCN095
set_option maxRecDepth 2048
set_option maxHeartbeats 300000
def middle (p:FlagDegree):ℕ:=p.yz+p.all
def total (p:FlagDegree):ℕ:=p.zOnly+p.yz+p.all
def Below (p q:FlagDegree):Prop:=
  p.all ≤ q.all∧middle p ≤ middle q∧total p ≤ total q
def cap (t y s:ℕ):FlagDegree:=⟨t-y,y-s,s⟩
theorem cap_cumulative (t y s:ℕ) (hsy:s ≤ y) (hyt:y ≤ t):
    (cap t y s).all=s∧middle (cap t y s)=y∧total (cap t y s)=t:=by
  dsimp [cap,middle,total]
  omega
theorem mixed_expansion (p q r:FlagDegree):
    flagMixed p q r=
      (q.all*r.all+q.yz*r.all+q.all*r.yz)*total p+
      (q.zOnly*r.all+q.all*r.zOnly)*middle p+
      (q.yz*r.yz+q.zOnly*r.yz+q.yz*r.zOnly)*p.all:=by
  simp only [flagMixed,middle,total]
  ring
theorem mixed_mono_first {p P:FlagDegree} (h:Below p P) (q r:FlagDegree):
    flagMixed p q r ≤ flagMixed P q r:=by
  rw [mixed_expansion p q r,mixed_expansion P q r]
  exact Nat.add_le_add
    (Nat.add_le_add (Nat.mul_le_mul_left _ h.2.2) (Nat.mul_le_mul_left _ h.2.1))
    (Nat.mul_le_mul_left _ h.1)
theorem mixed_mono_second (p:FlagDegree) {q Q:FlagDegree}
    (h:Below q Q) (r:FlagDegree):flagMixed p q r ≤ flagMixed p Q r:=by
  calc
    flagMixed p q r=flagMixed q p r:=by unfold flagMixed;ring
    _ ≤ flagMixed Q p r:=mixed_mono_first h p r
    _=flagMixed p Q r:=by unfold flagMixed;ring
theorem mixed_mono_third (p q:FlagDegree) {r R:FlagDegree}
    (h:Below r R):flagMixed p q r ≤ flagMixed p q R:=by
  calc
    flagMixed p q r=flagMixed r q p:=by unfold flagMixed;ring
    _ ≤ flagMixed R q p:=mixed_mono_first h q p
    _=flagMixed p q R:=by unfold flagMixed;ring
theorem mixed_mono_tails (p:FlagDegree) {q Q r R:FlagDegree}
    (hq:Below q Q) (hr:Below r R):flagMixed p q r ≤ flagMixed p Q R:=
  (mixed_mono_second p hq r).trans (mixed_mono_third p Q hr)
theorem sum_mixed_le {I:Type*} [Fintype I]
    (p:I → FlagDegree) (P q r:FlagDegree)
    (hs:(∑ i,(p i).all) ≤ P.all)
    (hy:(∑ i,middle (p i)) ≤ middle P)
    (ht:(∑ i,total (p i)) ≤ total P):
    (∑ i,flagMixed (p i) q r) ≤ flagMixed P q r:=by
  rw [Finset.sum_congr rfl (fun i _ => mixed_expansion (p i) q r),
    mixed_expansion P q r]
  simp only [Finset.sum_add_distrib, ←Finset.mul_sum]
  exact Nat.add_le_add
    (Nat.add_le_add (Nat.mul_le_mul_left _ ht) (Nat.mul_le_mul_left _ hy))
    (Nat.mul_le_mul_left _ hs)
def padS (p:FlagDegree):ℕ:=max p.all 2
def padY (p:FlagDegree):ℕ:=max (middle p) (padS p+1)
def padT (p:FlagDegree):ℕ:=max (total p) (padY p)
def paddedTail (p:FlagDegree) (d:ℕ):FlagDegree:=
  ⟨2*(padT p-padY p)*d,
    1+2*(padY p-padS p)*d,
    2*(padS p-1)*d⟩
def paddedCost (d e:ℕ) (p:FlagDegree):ℕ:=
  flagMixed p (paddedTail p d) (paddedTail p e)
theorem paddedTail_cumulative (p:FlagDegree) (d:ℕ):
    (paddedTail p d).all=2*(padS p-1)*d∧
    middle (paddedTail p d)=1+2*(padY p-1)*d∧
    total (paddedTail p d)=1+2*(padT p-1)*d:=by
  have hs:1 ≤ padS p:=by
    have h:2 ≤ padS p:=le_max_right _ _
    omega
  have hy:padS p+1 ≤ padY p:=le_max_right _ _
  have ht:padY p ≤ padT p:=le_max_right _ _
  have hyadd:padY p-padS p+(padS p-1)=padY p-1:=by omega
  have htadd:padT p-padY p+(padY p-padS p)+(padS p-1)=
      padT p-1:=by omega
  refine ⟨rfl,?_,?_⟩
  · change (1+2*(padY p-padS p)*d)+2*(padS p-1)*d=_
    calc
      _=1+2*(padY p-padS p+(padS p-1))*d:=by ring
      _=_:=by rw [hyadd]
  · change (2*(padT p-padY p)*d+
      (1+2*(padY p-padS p)*d))+2*(padS p-1)*d=_
    calc
      _=1+2*(padT p-padY p+(padY p-padS p)+
        (padS p-1))*d:=by ring
      _=_:=by rw [htadd]
theorem padding_mono {p q:FlagDegree} (h:Below p q):
    padS p ≤ padS q∧padY p ≤ padY q∧padT p ≤ padT q:=by
  have hs:padS p ≤ padS q:=max_le_max h.1 (Nat.le_refl 2)
  have hy:padY p ≤ padY q:=max_le_max h.2.1 (Nat.add_le_add_right hs 1)
  have ht:padT p ≤ padT q:=max_le_max h.2.2 hy
  exact ⟨hs,hy,ht⟩
theorem paddedTail_mono (d:ℕ) {p q:FlagDegree} (h:Below p q):
    Below (paddedTail p d) (paddedTail q d):=by
  have hp:=paddedTail_cumulative p d
  have hq:=paddedTail_cumulative q d
  have hc:=padding_mono h
  have hm {a b:ℕ} (hab:a ≤ b):2*(a-1)*d ≤ 2*(b-1)*d:=
    Nat.mul_le_mul_right d (Nat.mul_le_mul_left 2 (Nat.sub_le_sub_right hab 1))
  unfold Below
  rw [hp.1,hp.2.1,hp.2.2,hq.1,hq.2.1,hq.2.2]
  exact ⟨hm hc.1,Nat.add_le_add_left (hm hc.2.1) 1,
    Nat.add_le_add_left (hm hc.2.2) 1⟩
theorem paddedCost_mono (d e:ℕ) {p q:FlagDegree} (h:Below p q):
    paddedCost d e p ≤ paddedCost d e q:=by
  exact (mixed_mono_first h _ _).trans
    (mixed_mono_tails q (paddedTail_mono d h) (paddedTail_mono e h))
theorem merge_padded_costs {I:Type*} [Fintype I]
    (d e:ℕ) (p:I → FlagDegree) (P:FlagDegree)
    (hs:(∑ i,(p i).all) ≤ P.all)
    (hy:(∑ i,middle (p i)) ≤ middle P)
    (ht:(∑ i,total (p i)) ≤ total P):
    (∑ i,paddedCost d e (p i)) ≤ paddedCost d e P:=by
  classical
  have hi (i:I):Below (p i) P:=by
    exact ⟨(Finset.single_le_sum (fun _ _ => Nat.zero_le _) (Finset.mem_univ i)).trans hs,
      (Finset.single_le_sum (fun _ _ => Nat.zero_le _) (Finset.mem_univ i)).trans hy,
      (Finset.single_le_sum (fun _ _ => Nat.zero_le _) (Finset.mem_univ i)).trans ht⟩
  calc
    (∑ i,paddedCost d e (p i)) ≤
        ∑ i,flagMixed (p i) (paddedTail P d) (paddedTail P e):=
      Finset.sum_le_sum (fun i _ =>
        mixed_mono_tails (p i) (paddedTail_mono d (hi i)) (paddedTail_mono e (hi i)))
    _ ≤ paddedCost d e P:=sum_mixed_le p P _ _ hs hy ht
theorem sum_mixed_le_finset {I:Type*} (s:Finset I)
    (p:I → FlagDegree) (P q r:FlagDegree)
    (hs:(∑ i∈s,(p i).all) ≤ P.all)
    (hy:(∑ i∈s,middle (p i)) ≤ middle P)
    (ht:(∑ i∈s,total (p i)) ≤ total P):
    (∑ i∈s,flagMixed (p i) q r) ≤ flagMixed P q r:=by
  rw [Finset.sum_congr rfl (fun i _ => mixed_expansion (p i) q r),
    mixed_expansion P q r]
  simp only [Finset.sum_add_distrib, ←Finset.mul_sum]
  exact Nat.add_le_add
    (Nat.add_le_add (Nat.mul_le_mul_left _ ht) (Nat.mul_le_mul_left _ hy))
    (Nat.mul_le_mul_left _ hs)
theorem merge_padded_costs_finset {I:Type*} (s:Finset I)
    (d e:ℕ) (p:I → FlagDegree) (P:FlagDegree)
    (hs:(∑ i∈s,(p i).all) ≤ P.all)
    (hy:(∑ i∈s,middle (p i)) ≤ middle P)
    (ht:(∑ i∈s,total (p i)) ≤ total P):
    (∑ i∈s,paddedCost d e (p i)) ≤ paddedCost d e P:=by
  classical
  have hi (i:I) (h:i∈s):Below (p i) P:=by
    exact ⟨(Finset.single_le_sum (fun _ _ => Nat.zero_le _) h).trans hs,
      (Finset.single_le_sum (fun _ _ => Nat.zero_le _) h).trans hy,
      (Finset.single_le_sum (fun _ _ => Nat.zero_le _) h).trans ht⟩
  calc
    (∑ i∈s,paddedCost d e (p i)) ≤
        ∑ i∈s,flagMixed (p i) (paddedTail P d) (paddedTail P e):=
      Finset.sum_le_sum (fun i h => mixed_mono_tails (p i)
        (paddedTail_mono d (hi i h)) (paddedTail_mono e (hi i h)))
    _ ≤ paddedCost d e P:=sum_mixed_le_finset s p P _ _ hs hy ht
theorem paddedTail_cap (t y s d:ℕ)
    (hs:2 ≤ s) (hy:s+1 ≤ y) (ht:y ≤ t):
    paddedTail (cap t y s) d=
      ⟨2*(t-y)*d,1+2*(y-s)*d,2*(s-1)*d⟩:=by
  have hc:=cap_cumulative t y s (by omega) ht
  have hps:padS (cap t y s)=s:=by
    change max s 2=s
    exact max_eq_left hs
  have hpy:padY (cap t y s)=y:=by
    unfold padY
    rw [hc.2.1,hps,max_eq_left hy]
  have hpt:padT (cap t y s)=t:=by
    unfold padT
    rw [hc.2.2,hpy,max_eq_left ht]
  simp only [paddedTail,hps,hpy,hpt]
private abbrev lowCap6751:ℕ:=261420997282933785
theorem all_le_middle (p:FlagDegree):p.all ≤ middle p:=by
  dsimp [middle]
  omega
theorem middle_le_total (p:FlagDegree):middle p ≤ total p:=by
  dsimp [middle,total]
  omega
theorem all_le_total (p:FlagDegree):p.all ≤ total p:=
  (all_le_middle p).trans (middle_le_total p)
theorem below_cap_of_bounds (p:FlagDegree) (t y s:ℕ)
    (hsy:s ≤ y) (hyt:y ≤ t)
    (hs:p.all ≤ s) (hy:middle p ≤ y) (ht:total p ≤ t):
    Below p (cap t y s):=by
  have hc:=cap_cumulative t y s hsy hyt
  unfold Below
  rw [hc.1,hc.2.1,hc.2.2]
  exact ⟨hs,hy,ht⟩
private theorem below_total_flag (p:FlagDegree):
    Below p ⟨0,0,total p⟩:=by
  unfold Below
  refine ⟨all_le_total p,?_,?_⟩
  · simpa only [middle,Nat.zero_add] using middle_le_total p
  · simp only [total,Nat.zero_add,le_refl]
private def diagonalRate (u s:ℕ):ℕ:=
  flagMixed ⟨0,0,1⟩
    (paddedTail (cap u u s) 131072)
    (paddedTail (cap u u s) 131073)
private theorem cost_le_diagonal_rate (p:FlagDegree) (u s:ℕ)
    (h:Below p (cap u u s)):
    paddedCost 131072 131073 p ≤ diagonalRate u s*total p:=by
  calc
    _ ≤ flagMixed p (paddedTail (cap u u s) 131072)
        (paddedTail (cap u u s) 131073):=
      mixed_mono_tails p (paddedTail_mono 131072 h) (paddedTail_mono 131073 h)
    _ ≤ flagMixed ⟨0,0,total p⟩ (paddedTail (cap u u s) 131072)
        (paddedTail (cap u u s) 131073):=
      mixed_mono_first (below_total_flag p) _ _
    _=diagonalRate u s*total p:=by
      simp only [diagonalRate,flagMixed]
      ring
private theorem affine64 (t:ℕ) (ht:64 ≤ t):
    paddedCost 131072 131073 (cap t 64 7)+5324494425030747=
      157093929156634*t:=by
  have hsub:t-64+64=t:=Nat.sub_add_cancel ht
  unfold paddedCost
  rw [paddedTail_cap t 64 7 131072 (by decide) (by decide) ht,
    paddedTail_cap t 64 7 131073 (by decide) (by decide) ht]
  simp only [cap,flagMixed]
  ring_nf
  omega
private theorem rate_of_affine {t c top alpha deficit:ℕ}
    (ht:t ≤ 1698) (hc:c+deficit=alpha*t)
    (hTop:top+deficit=alpha*1698) (hbound:top ≤ lowCap6751):
    1698*c ≤ lowCap6751*t:=by
  have hscaled:1698*c+deficit*t ≤ top*t+deficit*t:=by
    calc
      _ ≤ 1698*c+deficit*1698:=
        Nat.add_le_add_left (Nat.mul_le_mul_left deficit ht) _
      _=(c+deficit)*1698:=by ring
      _=(alpha*t)*1698:=by rw [hc]
      _=(alpha*1698)*t:=by ring
      _=(top+deficit)*t:=by rw [←hTop]
      _=top*t+deficit*t:=by ring
  exact (Nat.le_of_add_le_add_right hscaled).trans
    (Nat.mul_le_mul_right t hbound)
private theorem large_rate64 (t:ℕ) (hlo:64 ≤ t) (hhi:t ≤ 1698):
    1698*paddedCost 131072 131073 (cap t 64 7) ≤ lowCap6751*t:=by
  have htop:=affine64 1698 (by decide)
  have hb:paddedCost 131072 131073 (cap 1698 64 7) ≤ lowCap6751:=by
    unfold lowCap6751
    omega
  exact rate_of_affine hhi (affine64 t hlo) htop hb
private theorem middle_tail_formula64 (p:FlagDegree):
    flagMixed p (paddedTail (cap 64 64 7) 131072)
        (paddedTail (cap 64 64 7) 131073)=
      49478403883020*total p+223271313211507*p.all:=by
  norm_num [paddedTail,padT,padY,padS,cap,total,middle,flagMixed]
  ring
private theorem middle_rate64 (t:ℕ) (ht:15 ≤ t):
    1698*(49478403883020*t+223271313211507*7) ≤ lowCap6751*t:=by
  unfold lowCap6751
  omega
theorem rate_bound_6751_low (p:FlagDegree)
    (hs:p.all ≤ 7) (hy:middle p ≤ 64) (ht:total p ≤ 1698):
    1698*paddedCost 131072 131073 p ≤ 261420997282933785*total p:=by
  have hn:=middle_le_total p
  by_cases ht15:total p ≤ 15
  · have hb:=below_cap_of_bounds p 15 15 7 (by decide) (by decide)
      hs (hn.trans ht15) ht15
    have hc:=cost_le_diagonal_rate p 15 7 hb
    have hk:1698*diagonalRate 15 7 ≤ 261420997282933785:=by decide
    calc
      _ ≤ 1698*(diagonalRate 15 7*total p):=Nat.mul_le_mul_left 1698 hc
      _=(1698*diagonalRate 15 7)*total p:=by ring
      _ ≤ _:=Nat.mul_le_mul_right (total p) hk
  · by_cases ht64:total p ≤ 64
    · have hb:=below_cap_of_bounds p 64 64 7 (by decide) (by decide) hs hy ht64
      have hc:paddedCost 131072 131073 p ≤
          49478403883020*total p+223271313211507*7:=by
        calc
          _ ≤ flagMixed p (paddedTail (cap 64 64 7) 131072)
              (paddedTail (cap 64 64 7) 131073):=
            mixed_mono_tails p (paddedTail_mono 131072 hb) (paddedTail_mono 131073 hb)
          _=49478403883020*total p+223271313211507*p.all:=
            middle_tail_formula64 p
          _ ≤ _:=Nat.add_le_add_left (Nat.mul_le_mul_left _ hs) _
      exact (Nat.mul_le_mul_left 1698 hc).trans (middle_rate64 (total p) (by omega))
    · have hlo:64 ≤ total p:=by omega
      have hb:=below_cap_of_bounds p (total p) 64 7 (by decide) hlo hs hy (le_refl _)
      exact (Nat.mul_le_mul_left 1698 (paddedCost_mono 131072 131073 hb)).trans
        (large_rate64 (total p) hlo ht)
theorem aggregate_6751_low {I:Type*} [Fintype I] (p:I → FlagDegree)
    (hs:∀ i,(p i).all ≤ 7) (hy:∀ i,middle (p i) ≤ 64)
    (htsum:(∑ i,total (p i)) ≤ 1698):
    (∑ i,paddedCost 131072 131073 (p i)) ≤ 261420997282933785:=by
  classical
  have hti (i:I):total (p i) ≤ 1698:=
    (Finset.single_le_sum (fun _ _ => Nat.zero_le _) (Finset.mem_univ i)).trans htsum
  have hscaled:1698*(∑ i,paddedCost 131072 131073 (p i)) ≤
      1698*261420997282933785:=by
    calc
      _=∑ i,1698*paddedCost 131072 131073 (p i):=by rw [Finset.mul_sum]
      _ ≤ ∑ i,261420997282933785*total (p i):=
        Finset.sum_le_sum (fun i _ => rate_bound_6751_low (p i) (hs i) (hy i) (hti i))
      _=261420997282933785*(∑ i,total (p i)):=by rw [Finset.mul_sum]
      _ ≤ 261420997282933785*1698:=Nat.mul_le_mul_left _ htsum
      _=1698*261420997282933785:=by ring
  exact Nat.le_of_mul_le_mul_left hscaled (by decide)
end ProximityPrize.SubmissionLower.LocatorFactorAggregate
