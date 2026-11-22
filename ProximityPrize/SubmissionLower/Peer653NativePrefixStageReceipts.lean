import ProximityPrize.SubmissionLower.Peer653NativePrefixStages
import ProximityPrize.SubmissionLower.Peer653NativePrefixData

set_option Elab.async false
set_option autoImplicit true
set_option maxRecDepth 18000

namespace Peer653NativePrefixStages

open Peer653NativePrefix
open Peer653NativePrefixStages (BankCertificate checked of_certificate)
open K1_14 (Shape)
open P3 (p)

private def Checks (lo : ℕ) (ss : List Stage) : Prop :=
  ∀ s ∈ ss, BankCertificate lo s.reserve 0 s.free ∧ BankCertificate lo s.reserve 1 s.moving
private theorem nil {lo : ℕ} : Checks lo [] := fun _ hs => (List.not_mem_nil hs).elim
private theorem cons {lo : ℕ} {s : Stage} {ss : List Stage}
    (hf : BankCertificate lo s.reserve 0 s.free)
    (hm : BankCertificate lo s.reserve 1 s.moving)
    (ht : Checks lo ss) : Checks lo (s::ss) :=
  List.forall_mem_cons.mpr ⟨⟨hf, hm⟩, ht⟩
set_option quotPrecheck false

local notation "bank!" kk "," ww "," zz "," dd =>
  checked (k := kk) (w := ww) (z := zz) (d := dd)
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide) (by decide) (by decide) (by decide) (by decide)

private theorem certificates (b : Band) : Checks (start b) (stages b) := by
  cases b with
  | h2390 =>
    rw [stages]
    refine cons (bank! 106,160591,0x602629320,0x82b954b820) (bank! 607,376504,0x8ae125c83390,0x52dc4f99d91a60) ?_
    refine cons (bank! 116,128273,0xc6acd70cc,0xc92d8e7778) (bank! 605,449190,0x7fa6ffc8cfb0,0x74d94c1652d2fc) ?_
    refine cons (bank! 128,198385,0x5e04496c00,0x125e78668f0) (bank! 705,528822,0xcaa11231e8e8,0xbf0ad385de03e8) ?_
    refine cons (bank! 138,166067,0x87e162a9e4,0x1a4d0027bc0) (bank! 683,219326,0xd99aeffdeb0,0x1031f4e7dd5ddf0) ?_
    refine cons (bank! 149,184964,0x5b268ffee0,0x2493c5a98d0) (bank! 729,360469,0x15b72436c5a54,0x1712f0ca90233c4) ?_
    refine cons (bank! 162,126395,0xaa5a877408,0x32223b38ad0) (bank! 891,685880,0x21fd9e8ad01f4,0x240a89f89589228) ?_
    refine cons (bank! 176,114261,0x31e5c5faa0,0x5b93fd34c60) (bank! 950,690988,0x35f22fea7df40,0x3d7bfa710a79018) ?_
    refine cons (bank! 198,147275,0x1f0701b6670,0xd35e7e95c50) (bank! 1200,887678,0x881c532683a00,0x9618db7093bb040) ?_
    refine cons (bank! 238,188339,0x189cfd315bc,0x4bf2c2579710) (bank! 1406,640492,0x459ce5bb3bd94,0x1e1fa40af4c36814) ?_
    refine cons (bank! 248,189481,0x280f102ea80,0xc9ef4efe878) (bank! 1099,752051,0x780adec6c0968,0x86458a2297529d0) ?_
    refine cons (bank! 348,226093,0x9f4b3b05f98,0x4f7b51ab4a0c) (bank! 1806,572977,0xd93c1ddbeefe0,0x46218f1c7f469ab0) ?_
    refine cons (bank! 363,217374,0x1766d5b2aa40,0x3518591f65260) (bank! 2023,449469,0x399346f7878c50,0x14f409c9a6a1cfc54) ?_
    refine cons (bank! 479,406422,0xb545dc5a85c,0x164041bf02f1c) (bank! 2224,802969,0x2aa70270827d04,0x11ea0b364366b23cc) ?_
    refine cons (bank! 523,259094,0x2ded3aa85840,0x5afa6733852e8) (bank! 3124,779666,0x1ba0b9b9f85baa8,0x4bca9c8888e1d4f40) ?_
    refine cons (bank! 832,474853,0x19d52af2fc150,0x2a53f7a5abba18) (bank! 4833,992813,0x433e5ae51fb869c,0x289814b8560055f6c0) ?_
    refine cons (bank! 693,177676,0x49109214d560,0x14d83acb4299400) (bank! 3826,727830,0x5a1c27ba0f46b8,0x3926fd85086585e148) ?_
    refine cons (bank! 1127,148718,0x7efcf3f8b71fc,0xc416d01948dcac) (bank! 6619,414937,0x7eb1c32eb51cbb8,0xbfbd30cbd84ebd3c08) ?_
    exact nil

theorem stage_bounds (b : Band) {s : Stage} (hs : s ∈ stages b)
    {h : ℕ} (hl : start b ≤ h) (hh : h ≤ 131071) :
    (WidthGuard h s.reserve s.free.shape ∧
      debit h s.free < gain h s.reserve s.free.shape 0 ∧ s.free.shape.U < p) ∧
    (WidthGuard h s.reserve s.moving.shape ∧
      debit h s.moving < gain h s.reserve s.moving.shape 1 ∧ s.moving.shape.U < p) := by
  obtain ⟨hf,hm⟩ := certificates b s hs
  exact ⟨of_certificate hl hh hf, of_certificate hl hh hm⟩

#print axioms stage_bounds
end Peer653NativePrefixStages
