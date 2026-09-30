import ProximityPrize.SubmissionLower.PackingCheck6815
namespace ProximityPrize.SubmissionLower.PackingSemantics6815
open PackingCheck6815
open FinalCurves6815
set_option autoImplicit false
set_option maxHeartbeats 2200000
set_option maxRecDepth 100000

def decodeNatList (radix : ℕ) : ℕ → ℕ → List ℕ
  | 0,_ => []
  | n+1,c => c%radix :: decodeNatList radix n (c/radix)
def natRow (n bits code : ℕ) : Array ℕ := (decodeNatList (2^bits) n code).toArray
def lookup (rows : ℕ → Array ℕ) (r v : ℕ) := ((rows r)[v]?).getD 0

theorem direct_bellman (Rcap Ycap : ℕ) (own packed : ℕ → Array ℕ)
    (ho : ∀ r, 1≤r → r≤Rcap → (own r).size=Ycap+1-r)
    (hp : ∀ r, r≤Rcap → (packed r).size=Ycap+1-r)
    (hc : ∀ R r, 1≤r → r≤R → R≤Rcap →
      convolution (own r).toList (packed (R-r)).toList (packed R).toList=true) :
    AffineFactorAggregate6808.BellmanRows Rcap Ycap (lookup own) (lookup packed) := by
  intro r v R V hr hR hY
  have he : r+R-r=R := by omega
  have hh := hc (r+R) r hr (by omega) hR
  rw [he] at hh
  have h := convolution_sound (own r).toList (packed R).toList (packed (r+R)).toList hh v V
    (by rw [Array.length_toList,ho r hr (by omega)]; omega)
    (by rw [Array.length_toList,hp R (by omega)]; omega)
    (by rw [Array.length_toList,hp (r+R) hR]; omega)
  simpa only [Array.getElem?_toList,lookup] using h

theorem rectangular_bellman (Rcap Vcap : ℕ) (own packed : ℕ → Array ℕ)
    (ho : ∀ r, 1≤r → r≤Rcap → (own r).size=Vcap+1)
    (hp : ∀ r, r≤Rcap → (packed r).size=Vcap+1)
    (hc : ∀ R r, 1≤r → r≤R → R≤Rcap →
      convolution (own r).toList (packed (R-r)).toList (packed R).toList=true) :
    RectangularPacking6815.Bellman Rcap Vcap (lookup own) (lookup packed) := by
  intro r v R V hr hR hV
  have he : r+R-r=R := by omega
  have hh := hc (r+R) r hr (by omega) hR
  rw [he] at hh
  have h := convolution_sound (own r).toList (packed R).toList (packed (r+R)).toList hh v V
    (by rw [Array.length_toList,ho r hr (by omega)]; omega)
    (by rw [Array.length_toList,hp R (by omega)]; omega)
    (by rw [Array.length_toList,hp (r+R) hR]; omega)
  simpa only [Array.getElem?_toList,lookup] using h

def checkRow (own packed : ℕ → Array ℕ) (R : ℕ) : Bool :=
  SingletonCertificate6815.allN (fun j => convolution (own (j+1)).toList
    (packed (R-(j+1))).toList (packed R).toList) R

def affineCheck (slope base : ℕ) (curve : List Piece) : Bool :=
  allCells (fun lo p => Nat.ble p.base (slope*lo+base) &&
    Nat.ble (value p lo (p.stop-1)) (slope*(p.stop-1)+base)) 0 curve

theorem affineCheck_sound (slope base finish : ℕ) (curve : List Piece)
    (hv : validFrom finish 0 curve=true) (hc : affineCheck slope base curve=true)
    (z : ℕ) (hz : z<finish) : eval curve z≤slope*z+base := by
  apply pointwise_of_cells (fun z value => value≤slope*z+base) 0 finish curve hv _ z (Nat.zero_le _) hz
  apply cells_mono _ _ 0 curve (allCells_sound _ 0 curve hc)
  intro lo p h x hlox hx
  simp only [Bool.and_eq_true,Nat.ble_eq] at h
  have hh := TriangularAffine6815.shifted_between lo (p.stop-1) x lo 0 p.base base p.slope slope
    le_rfl (Nat.zero_le _) hlox (by omega)
    (by simpa only [Nat.sub_self,Nat.mul_zero,Nat.add_zero,Nat.sub_zero,Nat.add_comm] using h.1)
    (by simpa only [value,Nat.sub_zero,Nat.add_comm] using h.2)
  simpa only [value,Nat.sub_zero,Nat.add_comm] using hh

end ProximityPrize.SubmissionLower.PackingSemantics6815
