module

public import Erdos272.Counting.N67702.WitnessHighLinks67702G0
public import Erdos272.Counting.N67702.WitnessHighLinks67702G1
public import Erdos272.Counting.N67702.WitnessHighLinks67702G10
public import Erdos272.Counting.N67702.WitnessHighLinks67702G11
public import Erdos272.Counting.N67702.WitnessHighLinks67702G12
public import Erdos272.Counting.N67702.WitnessHighLinks67702G13
public import Erdos272.Counting.N67702.WitnessHighLinks67702G14
public import Erdos272.Counting.N67702.WitnessHighLinks67702G15
public import Erdos272.Counting.N67702.WitnessHighLinks67702G16
public import Erdos272.Counting.N67702.WitnessHighLinks67702G17
public import Erdos272.Counting.N67702.WitnessHighLinks67702G18
public import Erdos272.Counting.N67702.WitnessHighLinks67702G2
public import Erdos272.Counting.N67702.WitnessHighLinks67702G3
public import Erdos272.Counting.N67702.WitnessHighLinks67702G4
public import Erdos272.Counting.N67702.WitnessHighLinks67702G5
public import Erdos272.Counting.N67702.WitnessHighLinks67702G6
public import Erdos272.Counting.N67702.WitnessHighLinks67702G7
public import Erdos272.Counting.N67702.WitnessHighLinks67702G8
public import Erdos272.Counting.N67702.WitnessHighLinks67702G9

@[expose] public section

namespace JSP233.WitnessHighSound67702
open WitnessHighSoundData67702
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option maxRecDepth 200000

abbrev row := WitnessHighSoundData67702.row
abbrev Witness := WitnessHighSoundData67702.Witness
abbrev length := @WitnessHighSoundData67702.length

theorem links {k : ℕ} (hk : k < 148) : Links k hk := by
  by_cases h0 : k < 8
  · exact WitnessHighLinks67702G0.links (by omega) h0
  by_cases h1 : k < 16
  · exact WitnessHighLinks67702G1.links (by omega) h1
  by_cases h2 : k < 24
  · exact WitnessHighLinks67702G2.links (by omega) h2
  by_cases h3 : k < 32
  · exact WitnessHighLinks67702G3.links (by omega) h3
  by_cases h4 : k < 40
  · exact WitnessHighLinks67702G4.links (by omega) h4
  by_cases h5 : k < 48
  · exact WitnessHighLinks67702G5.links (by omega) h5
  by_cases h6 : k < 56
  · exact WitnessHighLinks67702G6.links (by omega) h6
  by_cases h7 : k < 64
  · exact WitnessHighLinks67702G7.links (by omega) h7
  by_cases h8 : k < 72
  · exact WitnessHighLinks67702G8.links (by omega) h8
  by_cases h9 : k < 80
  · exact WitnessHighLinks67702G9.links (by omega) h9
  by_cases h10 : k < 88
  · exact WitnessHighLinks67702G10.links (by omega) h10
  by_cases h11 : k < 96
  · exact WitnessHighLinks67702G11.links (by omega) h11
  by_cases h12 : k < 104
  · exact WitnessHighLinks67702G12.links (by omega) h12
  by_cases h13 : k < 112
  · exact WitnessHighLinks67702G13.links (by omega) h13
  by_cases h14 : k < 120
  · exact WitnessHighLinks67702G14.links (by omega) h14
  by_cases h15 : k < 128
  · exact WitnessHighLinks67702G15.links (by omega) h15
  by_cases h16 : k < 136
  · exact WitnessHighLinks67702G16.links (by omega) h16
  by_cases h17 : k < 144
  · exact WitnessHighLinks67702G17.links (by omega) h17
  exact WitnessHighLinks67702G18.links (by omega) hk
#print axioms links

theorem high_value {k : ℕ} (hk : k < 148) :
    WitnessActualFamily80470.RowLight (row k) (length hk) (CleanupRows67702.data k).steps (Witness k)=
      WitnessHighNumeric67702.value (WitnessHighNumeric67702.data k) := by
  unfold WitnessActualFamily80470.RowLight WitnessHighNumeric67702.value WitnessHighNumeric80470.value
  rw [(links hk).1,(links hk).2.1]
  apply Finset.sum_congr rfl
  intro b hb
  rw [←(links hk).2.2 b]
  change (if (WitnessHighNumeric80470.band (WitnessHighNumeric67702.data k) b).E≤1 then 0 else _) = _
  by_cases he : (WitnessHighNumeric80470.band (WitnessHighNumeric67702.data k) b).E≤1
  · simp only [if_pos he]
  · simp only [if_neg he]
    apply Finset.sum_congr rfl
    intro d hd
    exact (WitnessHighSound80470.cost_eq _ _ _ _).symm
#print axioms high_value
end
end JSP233.WitnessHighSound67702
