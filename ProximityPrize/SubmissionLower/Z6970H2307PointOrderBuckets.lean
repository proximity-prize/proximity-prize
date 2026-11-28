import ProximityPrize.SubmissionLower.Z6970H2307OrderLookup
import ProximityPrize.SubmissionLower.Z6970H2307Bands
import ProximityPrize.SubmissionLower.Bundle6970_5e7bd3ab721b4cab
import ProximityPrize.SubmissionLower.Bundle6970_5e7bd3ab721b4cab
import ProximityPrize.SubmissionLower.Bundle6970_5e7bd3ab721b4cab
import ProximityPrize.SubmissionLower.Bundle6970_5e7bd3ab721b4cab
import ProximityPrize.SubmissionLower.Bundle6970_5e7bd3ab721b4cab
import ProximityPrize.SubmissionLower.Bundle6970_5e7bd3ab721b4cab
import ProximityPrize.SubmissionLower.Bundle6970_5e7bd3ab721b4cab
import ProximityPrize.SubmissionLower.Bundle6970_5e7bd3ab721b4cab
import ProximityPrize.SubmissionLower.Bundle6970_5e7bd3ab721b4cab
import ProximityPrize.SubmissionLower.Bundle6970_5e7bd3ab721b4cab
import ProximityPrize.SubmissionLower.Bundle6970_5e7bd3ab721b4cab
import ProximityPrize.SubmissionLower.Bundle6970_5e7bd3ab721b4cab
import ProximityPrize.SubmissionLower.Bundle6970_5e7bd3ab721b4cab
import ProximityPrize.SubmissionLower.Bundle6970_5e7bd3ab721b4cab
set_option maxHeartbeats 0
set_option maxRecDepth 30000
namespace Height2307PointOrder
open Height2307Orders
open Height2307Bands
def buckets : Nat → Array (List Threshold)
  | 0 => bucket0
  | 1 => bucket1
  | 2 => bucket2
  | 3 => bucket3
  | 4 => bucket4
  | 5 => bucket5
  | 6 => bucket6
  | 7 => bucket7
  | 8 => bucket8
  | 9 => bucket9
  | 10 => bucket10
  | 11 => bucket11
  | 12 => bucket12
  | 13 => bucket13
  | 14 => bucket14
  | 15 => bucket15
  | 16 => bucket16
  | 17 => bucket17
  | 18 => bucket18
  | 19 => bucket19
  | 20 => bucket20
  | 21 => bucket21
  | 22 => bucket22
  | 23 => bucket23
  | 24 => bucket24
  | 25 => bucket25
  | 26 => bucket26
  | 27 => bucket27
  | 28 => bucket28
  | 29 => bucket29
  | 30 => bucket30
  | 31 => bucket31
  | 32 => bucket32
  | 33 => bucket33
  | 34 => bucket34
  | 35 => bucket35
  | 36 => bucket36
  | 37 => bucket37
  | 38 => bucket38
  | 39 => bucket39
  | 40 => bucket40
  | 41 => bucket41
  | _ => #[]

theorem allBuckets (k : Band) : (buckets k.val).toList.flatten = thresholds k := by
  fin_cases k
  · exact flatten0
  · exact flatten1
  · exact flatten2
  · exact flatten3
  · exact flatten4
  · exact flatten5
  · exact flatten6
  · exact flatten7
  · exact flatten8
  · exact flatten9
  · exact flatten10
  · exact flatten11
  · exact flatten12
  · exact flatten13
  · exact flatten14
  · exact flatten15
  · exact flatten16
  · exact flatten17
  · exact flatten18
  · exact flatten19
  · exact flatten20
  · exact flatten21
  · exact flatten22
  · exact flatten23
  · exact flatten24
  · exact flatten25
  · exact flatten26
  · exact flatten27
  · exact flatten28
  · exact flatten29
  · exact flatten30
  · exact flatten31
  · exact flatten32
  · exact flatten33
  · exact flatten34
  · exact flatten35
  · exact flatten36
  · exact flatten37
  · exact flatten38
  · exact flatten39
  · exact flatten40
  · exact flatten41
theorem mem_of_bucket {k : Band} {i : Nat} {ps : List Threshold}
    (atIndex : (buckets k.val)[i]? = some ps) {p : Threshold} (hp : p ∈ ps) :
    p ∈ thresholds k := by
  rw [← allBuckets k, List.mem_flatten]
  exact ⟨ps, Array.mem_toList_iff.mpr (Array.mem_of_getElem? atIndex), hp⟩

end Height2307PointOrder
