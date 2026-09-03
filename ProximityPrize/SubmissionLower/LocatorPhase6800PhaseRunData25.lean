import ProximityPrize.SubmissionLower.LocatorPhase6800PhaseRuns
import ProximityPrize.SubmissionLower.LocatorPhase6800PhaseRunData21

namespace ProximityPrize.SubmissionLower.LocatorPhase6800PhaseRunData25

open LocatorPhase6800PhaseRuns

def runs : Array (Array (List PhaseRun)) := #[
  #[[], [], [⟨1, 0⟩, ⟨2, 0⟩, ⟨3, 0⟩, ⟨632, 0⟩], []],
  #[[], [], [⟨1, 0⟩, ⟨2, 0⟩, ⟨3, 0⟩, ⟨599, 0⟩], []],
  #[[], [], [⟨1, 0⟩, ⟨2, 0⟩, ⟨3, 0⟩, ⟨566, 0⟩], []],
  #[[], [], [⟨1, 0⟩, ⟨2, 0⟩, ⟨3, 0⟩, ⟨22, 0⟩, ⟨532, 0⟩], []],
  #[[], [], [⟨1, 0⟩, ⟨2, 0⟩, ⟨3, 0⟩, ⟨498, 0⟩], []],
  #[[], [], [⟨1, 0⟩, ⟨2, 0⟩, ⟨3, 0⟩, ⟨463, 0⟩], []],
  #[[], [], [⟨1, 0⟩, ⟨2, 0⟩, ⟨3, 0⟩, ⟨429, 0⟩], []],
  #[[], [], [⟨1, 0⟩, ⟨2, 0⟩, ⟨3, 0⟩, ⟨393, 0⟩], []],
  #[[], [], [⟨1, 0⟩, ⟨2, 0⟩, ⟨3, 0⟩, ⟨358, 0⟩], []],
  #[[], [], [⟨1, 0⟩, ⟨2, 0⟩, ⟨3, 0⟩, ⟨322, 0⟩], []],
  #[[], [], [⟨1, 0⟩, ⟨2, 0⟩, ⟨3, 0⟩, ⟨285, 0⟩], []],
  #[[], [], [⟨1, 0⟩, ⟨2, 0⟩, ⟨3, 0⟩, ⟨248, 0⟩], []],
  #[[], [], [⟨1, 0⟩, ⟨2, 0⟩, ⟨3, 0⟩, ⟨211, 0⟩], []],
  #[[], [], [⟨1, 0⟩, ⟨2, 0⟩, ⟨3, 0⟩, ⟨173, 0⟩], []],
  #[[], [], [⟨1, 0⟩, ⟨2, 0⟩, ⟨3, 0⟩, ⟨135, 0⟩], []],
  #[[], [], [⟨1, 0⟩, ⟨2, 0⟩, ⟨3, 0⟩, ⟨96, 0⟩], []],
  #[[], [], [⟨1, 0⟩, ⟨2, 0⟩, ⟨3, 0⟩, ⟨57, 0⟩], []],
  #[[], [], [⟨1, 0⟩, ⟨2, 0⟩, ⟨3, 0⟩, ⟨17, 0⟩], []],
  #[[], [], [], []],
  #[[], [], [], []],
  #[[], [], [], []],
  #[[], [], [], []],
  #[[], [], [], []],
  #[[], [], [], []],
  #[[], [], [], []],
  #[[], [], [], []],
  #[[], [], [], []],
  #[[], [], [], []],
  #[[], [], [], []],
  #[[], [], [], []],
  #[[], [], [], []],
  #[[], [], [], []],
  #[[], [], [], []],
  #[[], [], [], []],
  #[[], [], [], []],
  #[[], [], [], []],
  #[[], [], [], []],
  #[[], [], [], []],
  #[[], [], [], []],
  #[[], [], [], []],
  #[[], [], [], []],
  #[[], [], [], []],
  #[[], [], [], []],
  #[[], [], [], []],
  #[[], [], [], []],
  #[[], [], [], []],
  #[[], [], [], []],
  #[[], [], [], []],
  #[[], [], [], []],
  #[[], [], [], []],
  #[[], [], [], []],
  #[[], [], [], []],
  #[[], [], [], []],
  #[[], [], [], []],
  #[[], [], [], []],
  #[[], [], [], []],
  #[[], [], [], []],
  #[[], [], [], []],
  #[[], [], [], []],
  #[[], [], [], []],
  #[[], [], [], []],
  #[[], [], [], []],
  #[[], [], [], []],
  #[[], [], [], []],
  #[[], [], [], []],
  #[[], [], [], []],
  #[[], [], [], []],
  #[[], [], [], []],
  #[[], [], [], []],
  #[[], [], [], []],
  #[[], [], [], []],
  #[[], [], [], []],
  #[[], [], [], []],
  #[[], [], [], []],
  #[[], [], [], []],
  #[[], [], [], []],
  #[[], [], [], []],
  #[[], [], [], []],
  #[[], [], [], []],
  #[[], [], [], []],
  #[[], [], [], []],
  #[[], [], [], []],
  #[[], [], [], []],
  #[[], [], [], []],
  #[[], [], [], []],
  #[[], [], [], []],
  #[[], [], [], []],
  #[[], [], [], []],
  #[[], [], [], []],
  #[[], [], [], []],
  #[[], [], [], []],
  #[[], [], [], []],
  #[[], [], [], []],
  #[[], [], [], []],
  #[[], [], [], []],
  #[[], [], [], []],
  #[[], [], [], []],
  #[[], [], [], []],
  #[[], [], [], []],
  #[[], [], [], []],
  #[[], [], [], []],
  #[[], [], [], []],
  #[[], [], [], []]]

theorem validV000 :
    SparseRowValid (rowContext 25 0) ((runs[0]?).getD #[]) := by
  decide +kernel

theorem validV001 :
    SparseRowValid (rowContext 25 1) ((runs[1]?).getD #[]) := by
  decide +kernel

theorem validV002 :
    SparseRowValid (rowContext 25 2) ((runs[2]?).getD #[]) := by
  decide +kernel

theorem validV003 :
    SparseRowValid (rowContext 25 3) ((runs[3]?).getD #[]) := by
  decide +kernel

theorem validV004 :
    SparseRowValid (rowContext 25 4) ((runs[4]?).getD #[]) := by
  decide +kernel

theorem validV005 :
    SparseRowValid (rowContext 25 5) ((runs[5]?).getD #[]) := by
  decide +kernel

theorem validV006 :
    SparseRowValid (rowContext 25 6) ((runs[6]?).getD #[]) := by
  decide +kernel

theorem validV007 :
    SparseRowValid (rowContext 25 7) ((runs[7]?).getD #[]) := by
  decide +kernel

theorem validV008 :
    SparseRowValid (rowContext 25 8) ((runs[8]?).getD #[]) := by
  decide +kernel

theorem validV009 :
    SparseRowValid (rowContext 25 9) ((runs[9]?).getD #[]) := by
  decide +kernel

theorem validV010 :
    SparseRowValid (rowContext 25 10) ((runs[10]?).getD #[]) := by
  decide +kernel

theorem validV011 :
    SparseRowValid (rowContext 25 11) ((runs[11]?).getD #[]) := by
  decide +kernel

theorem validV012 :
    SparseRowValid (rowContext 25 12) ((runs[12]?).getD #[]) := by
  decide +kernel

theorem validV013 :
    SparseRowValid (rowContext 25 13) ((runs[13]?).getD #[]) := by
  decide +kernel

theorem validV014 :
    SparseRowValid (rowContext 25 14) ((runs[14]?).getD #[]) := by
  decide +kernel

theorem validV015 :
    SparseRowValid (rowContext 25 15) ((runs[15]?).getD #[]) := by
  decide +kernel

theorem validV016 :
    SparseRowValid (rowContext 25 16) ((runs[16]?).getD #[]) := by
  decide +kernel

theorem validV017 :
    SparseRowValid (rowContext 25 17) ((runs[17]?).getD #[]) := by
  decide +kernel

theorem validV018 :
    SparseRowValid (rowContext 25 18) ((runs[18]?).getD #[]) := by
  decide +kernel

theorem validV019 :
    SparseRowValid (rowContext 25 19) ((runs[19]?).getD #[]) := by
  decide +kernel

theorem validV020 :
    SparseRowValid (rowContext 25 20) ((runs[20]?).getD #[]) := by
  decide +kernel

theorem validV021 :
    SparseRowValid (rowContext 25 21) ((runs[21]?).getD #[]) := by
  decide +kernel

theorem validV022 :
    SparseRowValid (rowContext 25 22) ((runs[22]?).getD #[]) := by
  decide +kernel

theorem validV023 :
    SparseRowValid (rowContext 25 23) ((runs[23]?).getD #[]) := by
  decide +kernel

theorem validV024 :
    SparseRowValid (rowContext 25 24) ((runs[24]?).getD #[]) := by
  decide +kernel

theorem validV025 :
    SparseRowValid (rowContext 25 25) ((runs[25]?).getD #[]) := by
  decide +kernel

theorem validV026 :
    SparseRowValid (rowContext 25 26) ((runs[26]?).getD #[]) := by
  decide +kernel

theorem validV027 :
    SparseRowValid (rowContext 25 27) ((runs[27]?).getD #[]) := by
  decide +kernel

theorem validV028 :
    SparseRowValid (rowContext 25 28) ((runs[28]?).getD #[]) := by
  decide +kernel

theorem validV029 :
    SparseRowValid (rowContext 25 29) ((runs[29]?).getD #[]) := by
  decide +kernel

theorem validV030 :
    SparseRowValid (rowContext 25 30) ((runs[30]?).getD #[]) := by
  decide +kernel

theorem validV031 :
    SparseRowValid (rowContext 25 31) ((runs[31]?).getD #[]) := by
  decide +kernel

theorem validV032 :
    SparseRowValid (rowContext 25 32) ((runs[32]?).getD #[]) := by
  decide +kernel

theorem validV033 :
    SparseRowValid (rowContext 25 33) ((runs[33]?).getD #[]) := by
  decide +kernel

theorem validV034 :
    SparseRowValid (rowContext 25 34) ((runs[34]?).getD #[]) := by
  decide +kernel

theorem validV035 :
    SparseRowValid (rowContext 25 35) ((runs[35]?).getD #[]) := by
  decide +kernel

theorem validV036 :
    SparseRowValid (rowContext 25 36) ((runs[36]?).getD #[]) := by
  decide +kernel

theorem validV037 :
    SparseRowValid (rowContext 25 37) ((runs[37]?).getD #[]) := by
  decide +kernel

theorem validV038 :
    SparseRowValid (rowContext 25 38) ((runs[38]?).getD #[]) := by
  decide +kernel

theorem validV039 :
    SparseRowValid (rowContext 25 39) ((runs[39]?).getD #[]) := by
  decide +kernel

theorem validV040 :
    SparseRowValid (rowContext 25 40) ((runs[40]?).getD #[]) := by
  decide +kernel

theorem validV041 :
    SparseRowValid (rowContext 25 41) ((runs[41]?).getD #[]) := by
  decide +kernel

theorem validV042 :
    SparseRowValid (rowContext 25 42) ((runs[42]?).getD #[]) := by
  decide +kernel

theorem validV043 :
    SparseRowValid (rowContext 25 43) ((runs[43]?).getD #[]) := by
  decide +kernel

theorem validV044 :
    SparseRowValid (rowContext 25 44) ((runs[44]?).getD #[]) := by
  decide +kernel

theorem validV045 :
    SparseRowValid (rowContext 25 45) ((runs[45]?).getD #[]) := by
  decide +kernel

theorem validV046 :
    SparseRowValid (rowContext 25 46) ((runs[46]?).getD #[]) := by
  decide +kernel

theorem validV047 :
    SparseRowValid (rowContext 25 47) ((runs[47]?).getD #[]) := by
  decide +kernel

theorem validV048 :
    SparseRowValid (rowContext 25 48) ((runs[48]?).getD #[]) := by
  decide +kernel

theorem validV049 :
    SparseRowValid (rowContext 25 49) ((runs[49]?).getD #[]) := by
  decide +kernel

theorem validV050 :
    SparseRowValid (rowContext 25 50) ((runs[50]?).getD #[]) := by
  decide +kernel

theorem validV051 :
    SparseRowValid (rowContext 25 51) ((runs[51]?).getD #[]) := by
  decide +kernel

theorem validV052 :
    SparseRowValid (rowContext 25 52) ((runs[52]?).getD #[]) := by
  decide +kernel

theorem validV053 :
    SparseRowValid (rowContext 25 53) ((runs[53]?).getD #[]) := by
  decide +kernel

theorem validV054 :
    SparseRowValid (rowContext 25 54) ((runs[54]?).getD #[]) := by
  decide +kernel

theorem validV055 :
    SparseRowValid (rowContext 25 55) ((runs[55]?).getD #[]) := by
  decide +kernel

theorem validV056 :
    SparseRowValid (rowContext 25 56) ((runs[56]?).getD #[]) := by
  decide +kernel

theorem validV057 :
    SparseRowValid (rowContext 25 57) ((runs[57]?).getD #[]) := by
  decide +kernel

theorem validV058 :
    SparseRowValid (rowContext 25 58) ((runs[58]?).getD #[]) := by
  decide +kernel

theorem validV059 :
    SparseRowValid (rowContext 25 59) ((runs[59]?).getD #[]) := by
  decide +kernel

theorem validV060 :
    SparseRowValid (rowContext 25 60) ((runs[60]?).getD #[]) := by
  decide +kernel

theorem validV061 :
    SparseRowValid (rowContext 25 61) ((runs[61]?).getD #[]) := by
  decide +kernel

theorem validV062 :
    SparseRowValid (rowContext 25 62) ((runs[62]?).getD #[]) := by
  decide +kernel

theorem validV063 :
    SparseRowValid (rowContext 25 63) ((runs[63]?).getD #[]) := by
  decide +kernel

theorem validV064 :
    SparseRowValid (rowContext 25 64) ((runs[64]?).getD #[]) := by
  decide +kernel

theorem validV065 :
    SparseRowValid (rowContext 25 65) ((runs[65]?).getD #[]) := by
  decide +kernel

theorem validV066 :
    SparseRowValid (rowContext 25 66) ((runs[66]?).getD #[]) := by
  decide +kernel

theorem validV067 :
    SparseRowValid (rowContext 25 67) ((runs[67]?).getD #[]) := by
  decide +kernel

theorem validV068 :
    SparseRowValid (rowContext 25 68) ((runs[68]?).getD #[]) := by
  decide +kernel

theorem validV069 :
    SparseRowValid (rowContext 25 69) ((runs[69]?).getD #[]) := by
  decide +kernel

theorem validV070 :
    SparseRowValid (rowContext 25 70) ((runs[70]?).getD #[]) := by
  decide +kernel

theorem validV071 :
    SparseRowValid (rowContext 25 71) ((runs[71]?).getD #[]) := by
  decide +kernel

theorem validV072 :
    SparseRowValid (rowContext 25 72) ((runs[72]?).getD #[]) := by
  decide +kernel

theorem validV073 :
    SparseRowValid (rowContext 25 73) ((runs[73]?).getD #[]) := by
  decide +kernel

theorem validV074 :
    SparseRowValid (rowContext 25 74) ((runs[74]?).getD #[]) := by
  decide +kernel

theorem validV075 :
    SparseRowValid (rowContext 25 75) ((runs[75]?).getD #[]) := by
  decide +kernel

theorem validV076 :
    SparseRowValid (rowContext 25 76) ((runs[76]?).getD #[]) := by
  decide +kernel

theorem validV077 :
    SparseRowValid (rowContext 25 77) ((runs[77]?).getD #[]) := by
  decide +kernel

theorem validV078 :
    SparseRowValid (rowContext 25 78) ((runs[78]?).getD #[]) := by
  decide +kernel

theorem validV079 :
    SparseRowValid (rowContext 25 79) ((runs[79]?).getD #[]) := by
  decide +kernel

theorem validV080 :
    SparseRowValid (rowContext 25 80) ((runs[80]?).getD #[]) := by
  decide +kernel

theorem validV081 :
    SparseRowValid (rowContext 25 81) ((runs[81]?).getD #[]) := by
  decide +kernel

theorem validV082 :
    SparseRowValid (rowContext 25 82) ((runs[82]?).getD #[]) := by
  decide +kernel

theorem validV083 :
    SparseRowValid (rowContext 25 83) ((runs[83]?).getD #[]) := by
  decide +kernel

theorem validV084 :
    SparseRowValid (rowContext 25 84) ((runs[84]?).getD #[]) := by
  decide +kernel

theorem validV085 :
    SparseRowValid (rowContext 25 85) ((runs[85]?).getD #[]) := by
  decide +kernel

theorem validV086 :
    SparseRowValid (rowContext 25 86) ((runs[86]?).getD #[]) := by
  decide +kernel

theorem validV087 :
    SparseRowValid (rowContext 25 87) ((runs[87]?).getD #[]) := by
  decide +kernel

theorem validV088 :
    SparseRowValid (rowContext 25 88) ((runs[88]?).getD #[]) := by
  decide +kernel

theorem validV089 :
    SparseRowValid (rowContext 25 89) ((runs[89]?).getD #[]) := by
  decide +kernel

theorem validV090 :
    SparseRowValid (rowContext 25 90) ((runs[90]?).getD #[]) := by
  decide +kernel

theorem validV091 :
    SparseRowValid (rowContext 25 91) ((runs[91]?).getD #[]) := by
  decide +kernel

theorem validV092 :
    SparseRowValid (rowContext 25 92) ((runs[92]?).getD #[]) := by
  decide +kernel

theorem validV093 :
    SparseRowValid (rowContext 25 93) ((runs[93]?).getD #[]) := by
  decide +kernel

theorem validV094 :
    SparseRowValid (rowContext 25 94) ((runs[94]?).getD #[]) := by
  decide +kernel

theorem validV095 :
    SparseRowValid (rowContext 25 95) ((runs[95]?).getD #[]) := by
  decide +kernel

theorem validV096 :
    SparseRowValid (rowContext 25 96) ((runs[96]?).getD #[]) := by
  decide +kernel

theorem validV097 :
    SparseRowValid (rowContext 25 97) ((runs[97]?).getD #[]) := by
  decide +kernel

theorem validV098 :
    SparseRowValid (rowContext 25 98) ((runs[98]?).getD #[]) := by
  decide +kernel

theorem validV099 :
    SparseRowValid (rowContext 25 99) ((runs[99]?).getD #[]) := by
  decide +kernel

theorem validV100 :
    SparseRowValid (rowContext 25 100) ((runs[100]?).getD #[]) := by
  decide +kernel

theorem validV101 :
    SparseRowValid (rowContext 25 101) ((runs[101]?).getD #[]) := by
  decide +kernel

theorem validV102 :
    SparseRowValid (rowContext 25 102) ((runs[102]?).getD #[]) := by
  decide +kernel

theorem sparseStates :
    ∀ V ∈ List.range (128 - 25), SparsePhaseStateRVCheck (rowContext 25 V) := by
  intro V hV
  simp only [List.mem_range] at hV
  interval_cases V
  · exact validV000.sound
  · exact validV001.sound
  · exact validV002.sound
  · exact validV003.sound
  · exact validV004.sound
  · exact validV005.sound
  · exact validV006.sound
  · exact validV007.sound
  · exact validV008.sound
  · exact validV009.sound
  · exact validV010.sound
  · exact validV011.sound
  · exact validV012.sound
  · exact validV013.sound
  · exact validV014.sound
  · exact validV015.sound
  · exact validV016.sound
  · exact validV017.sound
  · exact validV018.sound
  · exact validV019.sound
  · exact validV020.sound
  · exact validV021.sound
  · exact validV022.sound
  · exact validV023.sound
  · exact validV024.sound
  · exact validV025.sound
  · exact validV026.sound
  · exact validV027.sound
  · exact validV028.sound
  · exact validV029.sound
  · exact validV030.sound
  · exact validV031.sound
  · exact validV032.sound
  · exact validV033.sound
  · exact validV034.sound
  · exact validV035.sound
  · exact validV036.sound
  · exact validV037.sound
  · exact validV038.sound
  · exact validV039.sound
  · exact validV040.sound
  · exact validV041.sound
  · exact validV042.sound
  · exact validV043.sound
  · exact validV044.sound
  · exact validV045.sound
  · exact validV046.sound
  · exact validV047.sound
  · exact validV048.sound
  · exact validV049.sound
  · exact validV050.sound
  · exact validV051.sound
  · exact validV052.sound
  · exact validV053.sound
  · exact validV054.sound
  · exact validV055.sound
  · exact validV056.sound
  · exact validV057.sound
  · exact validV058.sound
  · exact validV059.sound
  · exact validV060.sound
  · exact validV061.sound
  · exact validV062.sound
  · exact validV063.sound
  · exact validV064.sound
  · exact validV065.sound
  · exact validV066.sound
  · exact validV067.sound
  · exact validV068.sound
  · exact validV069.sound
  · exact validV070.sound
  · exact validV071.sound
  · exact validV072.sound
  · exact validV073.sound
  · exact validV074.sound
  · exact validV075.sound
  · exact validV076.sound
  · exact validV077.sound
  · exact validV078.sound
  · exact validV079.sound
  · exact validV080.sound
  · exact validV081.sound
  · exact validV082.sound
  · exact validV083.sound
  · exact validV084.sound
  · exact validV085.sound
  · exact validV086.sound
  · exact validV087.sound
  · exact validV088.sound
  · exact validV089.sound
  · exact validV090.sound
  · exact validV091.sound
  · exact validV092.sound
  · exact validV093.sound
  · exact validV094.sound
  · exact validV095.sound
  · exact validV096.sound
  · exact validV097.sound
  · exact validV098.sound
  · exact validV099.sound
  · exact validV100.sound
  · exact validV101.sound
  · exact validV102.sound

end ProximityPrize.SubmissionLower.LocatorPhase6800PhaseRunData25
