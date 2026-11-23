import ProximityPrize.SubmissionLower.KoalaH2429LocalSupport
import ProximityPrize.SubmissionLower.KoalaH2429Banks

set_option autoImplicit false
set_option maxRecDepth 16000
set_option maxHeartbeats 6000000

namespace KoalaH2429LocalSupport

def local14 : Data :=
  ⟨KoalaH2429Banks.stage12.free.shape, KoalaH2429Banks.stage12.moving.shape, KoalaH2429Banks.stage12.reserve,
    ![(140159/512), (8101669/841), (196327722/3703), (38204100/169)], ![83742, 2259, 605, 0], 75968746,
    (.splitX 2766 (.splitZ 168 (.splitX 1383 (.splitZ 84 (.splitX 691 (.leaf 49282) (.splitZ 42 (.leaf 65665) (.leaf 82050))) (.leaf 82050)) (.splitZ 84 (.splitX 2075 (.splitZ 42 (.leaf 82177) (.splitX 1729 (.leaf 82178) (.splitZ 63 (.leaf 82178) (.leaf 98562)))) (.leaf 98562)) (.splitX 2075 (.leaf 98562) (.splitZ 126 (.splitX 2421 (.leaf 98562) (.leaf 114946)) (.leaf 114947))))) (.leaf 131331)) (.leaf 131330))⟩
theorem local14_checked : Checked local14 := by decide +kernel

def local17 : Data :=
  ⟨KoalaH2429Banks.stage17.free.shape, KoalaH2429Banks.stage17.moving.shape, KoalaH2429Banks.stage17.reserve,
    ![(140159/512), (564083/81), (17643838981/474721), (38204100/169)], ![182796, 3094, 832, 0], 102016226,
    (.splitX 3694 (.splitZ 357 (.splitX 1847 (.splitZ 178 (.splitX 923 (.leaf 114947) (.leaf 147843)) (.leaf 180612)) (.splitZ 178 (.splitX 2771 (.splitZ 89 (.leaf 147843) (.leaf 180612)) (.splitZ 89 (.leaf 164355) (.splitX 3233 (.splitZ 134 (.leaf 180739) (.leaf 197124)) (.splitZ 134 (.leaf 197123) (.splitX 3464 (.splitZ 156 (.leaf 197124) (.leaf 213508)) (.leaf 213508)))))) (.splitX 2771 (.leaf 196996) (.splitZ 268 (.splitX 3233 (.leaf 213508) (.leaf 213508)) (.leaf 246278))))) (.leaf 278919)) (.splitZ 357 (.splitX 5542 (.splitZ 178 (.splitX 4618 (.splitZ 89 (.leaf 180739) (.splitX 4156 (.leaf 213508) (.leaf 213636))) (.leaf 230019)) (.splitX 4618 (.splitZ 268 (.splitX 4156 (.leaf 229892) (.leaf 230020)) (.leaf 262662)) (.leaf 246404))) (.leaf 262788)) (.leaf 311815)))⟩
theorem local17_checked : Checked local17 := by decide +kernel

def local20 : Data :=
  ⟨KoalaH2429Banks.stage20.free.shape, KoalaH2429Banks.stage20.moving.shape, KoalaH2429Banks.stage20.reserve,
    ![(4650542/22445), (54443131/8464), (19304458028/549081), (38204100/169)], ![384284, 2380, 632, 0], 116801772,
    (.splitX 5240 (.splitZ 515 (.splitX 2620 (.splitZ 257 (.splitX 1310 (.leaf 164229) (.leaf 213637)) (.leaf 262791)) (.splitZ 257 (.splitX 3930 (.splitZ 128 (.leaf 230021) (.leaf 262789)) (.splitZ 128 (.leaf 246533) (.splitX 4585 (.splitZ 193 (.leaf 279301) (.leaf 295686)) (.splitZ 193 (.leaf 295685) (.splitX 4913 (.splitZ 225 (.leaf 295686) (.leaf 312070)) (.splitZ 225 (.splitX 5077 (.leaf 295686) (.leaf 312070)) (.leaf 312070))))))) (.splitX 3930 (.leaf 295559) (.splitZ 386 (.splitX 4585 (.leaf 312071) (.leaf 328455)) (.leaf 377608))))) (.leaf 410250)) (.splitZ 515 (.splitX 7861 (.splitZ 257 (.splitX 6551 (.splitZ 128 (.leaf 263045) (.splitX 5896 (.splitZ 193 (.leaf 295813) (.splitX 5568 (.splitZ 225 (.leaf 312198) (.splitX 5404 (.leaf 312198) (.leaf 312198))) (.leaf 328582))) (.leaf 328581))) (.leaf 344965)) (.splitX 6551 (.splitZ 386 (.splitX 5896 (.leaf 328583) (.leaf 344967)) (.leaf 394120)) (.leaf 377735))) (.leaf 394245)) (.leaf 459658)))⟩
theorem local20_checked : Checked local20 := by decide +kernel

def local21 : Data :=
  ⟨KoalaH2429Banks.stage20.free.shape, KoalaH2429Banks.stage20.moving.shape, KoalaH2429Banks.stage20.reserve,
    ![(1564103/8410), (54443131/8464), (19304458028/549081), (38204100/169)], ![438444, 5264, 1411, 0], 163971729,
    (.splitX 5240 (.splitZ 515 (.splitX 2620 (.splitZ 257 (.splitX 1310 (.leaf 164229) (.leaf 213637)) (.leaf 262791)) (.splitZ 257 (.splitX 3930 (.splitZ 128 (.leaf 230021) (.leaf 262789)) (.splitZ 128 (.leaf 246533) (.splitX 4585 (.splitZ 193 (.leaf 279301) (.leaf 295686)) (.splitZ 193 (.leaf 295685) (.splitX 4913 (.splitZ 225 (.leaf 295686) (.leaf 312070)) (.splitZ 225 (.splitX 5077 (.leaf 295686) (.leaf 312070)) (.leaf 312070))))))) (.splitX 3930 (.leaf 295559) (.splitZ 386 (.splitX 4585 (.leaf 312071) (.leaf 328455)) (.leaf 377608))))) (.leaf 410250)) (.splitZ 515 (.splitX 7861 (.splitZ 257 (.splitX 6551 (.splitZ 128 (.leaf 263045) (.splitX 5896 (.splitZ 193 (.leaf 295813) (.splitX 5568 (.splitZ 225 (.leaf 312198) (.splitX 5404 (.leaf 312198) (.leaf 312198))) (.leaf 328582))) (.leaf 328581))) (.leaf 344965)) (.splitX 6551 (.splitZ 386 (.splitX 5896 (.leaf 328583) (.leaf 344967)) (.leaf 394120)) (.leaf 377735))) (.leaf 394245)) (.leaf 459658)))⟩
theorem local21_checked : Checked local21 := by decide +kernel

end KoalaH2429LocalSupport
