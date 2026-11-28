import ProximityPrize.SubmissionLower.Z6970PlateauNaturalSound

set_option autoImplicit false
namespace ExpandedPlateauNatural6970

theorem row_of_total (f v : ℕ) (hf : f ≤ 500)
    (h : columns f 0 ((1681-3*f)/2) = v) : ExpandedPlateauSum6970.chunk f 1 = (v:ℤ) :=
  (ExpandedPlateauSum6970.one_from_columns f).trans ((equivalent_columns f 0 _ hf).trans
    (congrArg (fun k : ℕ => (k:ℤ)) h))

end ExpandedPlateauNatural6970
