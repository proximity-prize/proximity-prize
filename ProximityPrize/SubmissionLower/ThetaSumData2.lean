import ProximityPrize.SubmissionLower.ThetaSumDefs

/-! Kernel-checked chunks of the theta savings sum (generated; values from the exact ledger). -/

namespace ThetaSum

theorem c1770 : chunk 1770 8 = 384386781 := by decide +kernel
theorem a1770 : chunk 1770 8 = 384386781 := c1770
theorem c1778 : chunk 1778 8 = 410932232 := by decide +kernel
theorem a1778 : chunk 1770 16 = 795319013 := by
  have h := chunk_join a1770 c1778
  exact h
theorem c1786 : chunk 1786 8 = 438896337 := by decide +kernel
theorem a1786 : chunk 1770 24 = 1234215350 := by
  have h := chunk_join a1778 c1786
  exact h
theorem c1794 : chunk 1794 8 = 467833662 := by decide +kernel
theorem a1794 : chunk 1770 32 = 1702049012 := by
  have h := chunk_join a1786 c1794
  exact h
theorem c1802 : chunk 1802 8 = 498210303 := by decide +kernel
theorem a1802 : chunk 1770 40 = 2200259315 := by
  have h := chunk_join a1794 c1802
  exact h
theorem c1810 : chunk 1810 8 = 529605758 := by decide +kernel
theorem a1810 : chunk 1770 48 = 2729865073 := by
  have h := chunk_join a1802 c1810
  exact h
theorem c1818 : chunk 1818 8 = 562409733 := by decide +kernel
theorem a1818 : chunk 1770 56 = 3292274806 := by
  have h := chunk_join a1810 c1818
  exact h
theorem c1826 : chunk 1826 8 = 596372105 := by decide +kernel
theorem a1826 : chunk 1770 64 = 3888646911 := by
  have h := chunk_join a1818 c1826
  exact h
theorem c1834 : chunk 1834 8 = 631551836 := by decide +kernel
theorem a1834 : chunk 1770 72 = 4520198747 := by
  have h := chunk_join a1826 c1834
  exact h
theorem c1842 : chunk 1842 8 = 668116646 := by decide +kernel
theorem a1842 : chunk 1770 80 = 5188315393 := by
  have h := chunk_join a1834 c1842
  exact h
theorem c1850 : chunk 1850 8 = 705808842 := by decide +kernel
theorem a1850 : chunk 1770 88 = 5894124235 := by
  have h := chunk_join a1842 c1850
  exact h
theorem c1858 : chunk 1858 8 = 744807551 := by decide +kernel
theorem a1858 : chunk 1770 96 = 6638931786 := by
  have h := chunk_join a1850 c1858
  exact h
theorem c1866 : chunk 1866 8 = 785126764 := by decide +kernel
theorem a1866 : chunk 1770 104 = 7424058550 := by
  have h := chunk_join a1858 c1866
  exact h
theorem c1874 : chunk 1874 8 = 826616236 := by decide +kernel
theorem a1874 : chunk 1770 112 = 8250674786 := by
  have h := chunk_join a1866 c1874
  exact h
theorem c1882 : chunk 1882 8 = 869337348 := by decide +kernel
theorem a1882 : chunk 1770 120 = 9120012134 := by
  have h := chunk_join a1874 c1882
  exact h
theorem c1890 : chunk 1890 8 = 913385852 := by decide +kernel
theorem a1890 : chunk 1770 128 = 10033397986 := by
  have h := chunk_join a1882 c1890
  exact h
theorem c1898 : chunk 1898 8 = 958624147 := by decide +kernel
theorem a1898 : chunk 1770 136 = 10992022133 := by
  have h := chunk_join a1890 c1898
  exact h
theorem c1906 : chunk 1906 8 = 1005047241 := by decide +kernel
theorem a1906 : chunk 1770 144 = 11997069374 := by
  have h := chunk_join a1898 c1906
  exact h
theorem c1914 : chunk 1914 8 = 1052649941 := by decide +kernel
theorem a1914 : chunk 1770 152 = 13049719315 := by
  have h := chunk_join a1906 c1914
  exact h
theorem c1922 : chunk 1922 8 = 1101457696 := by decide +kernel
theorem a1922 : chunk 1770 160 = 14151177011 := by
  have h := chunk_join a1914 c1922
  exact h
theorem c1930 : chunk 1930 8 = 1151435464 := by decide +kernel
theorem a1930 : chunk 1770 168 = 15302612475 := by
  have h := chunk_join a1922 c1930
  exact h
theorem c1938 : chunk 1938 8 = 1202520563 := by decide +kernel
theorem a1938 : chunk 1770 176 = 16505133038 := by
  have h := chunk_join a1930 c1938
  exact h
theorem c1946 : chunk 1946 8 = 1254696660 := by decide +kernel
theorem a1946 : chunk 1770 184 = 17759829698 := by
  have h := chunk_join a1938 c1946
  exact h
theorem c1954 : chunk 1954 8 = 1307935073 := by decide +kernel
theorem a1954 : chunk 1770 192 = 19067764771 := by
  have h := chunk_join a1946 c1954
  exact h
theorem c1962 : chunk 1962 8 = 1362201201 := by decide +kernel
theorem a1962 : chunk 1770 200 = 20429965972 := by
  have h := chunk_join a1954 c1962
  exact h
theorem c1970 : chunk 1970 8 = 1417457537 := by decide +kernel
theorem a1970 : chunk 1770 208 = 21847423509 := by
  have h := chunk_join a1962 c1970
  exact h

theorem part2 : chunk 1770 208 = 21847423509 := a1970

end ThetaSum
