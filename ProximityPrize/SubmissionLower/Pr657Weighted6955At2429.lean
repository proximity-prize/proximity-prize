import ProximityPrize.SubmissionLower.KoalaLow6954
import ProximityPrize.SubmissionLower.KoalaAt2428Rates

namespace Pr657Weighted6955At2429

theorem count {cap u del Γ} (M : P1.ModelAt cap u del)
    (F : P1.FamilyAt 179876 M Γ) (lo : 1 ≤ M.overhead)
    (hi : M.overhead ≤ 2429) (anchor : KoalaLow6954.Anchor Γ F.scalar) :
    Γ.card ≤ 273115485059352112 :=
  KoalaLow6954.count_with_anchor
    (fun _ _ _ hm f hf hact hon l hl hcut r hr hn =>
      KoalaAt2428Rates.count hm f hf hact hon l hl hcut r hr hn) M F lo hi anchor

#print axioms count
end Pr657Weighted6955At2429
