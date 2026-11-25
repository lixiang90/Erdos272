module

public import Erdos272.Arithmetic.N67702.SourceAtlasChecks67702G0
public import Erdos272.Arithmetic.N67702.SourceAtlasChecks67702G1
public import Erdos272.Arithmetic.N67702.SourceAtlasChecks67702G10
public import Erdos272.Arithmetic.N67702.SourceAtlasChecks67702G11
public import Erdos272.Arithmetic.N67702.SourceAtlasChecks67702G12
public import Erdos272.Arithmetic.N67702.SourceAtlasChecks67702G13
public import Erdos272.Arithmetic.N67702.SourceAtlasChecks67702G14
public import Erdos272.Arithmetic.N67702.SourceAtlasChecks67702G15
public import Erdos272.Arithmetic.N67702.SourceAtlasChecks67702G16
public import Erdos272.Arithmetic.N67702.SourceAtlasChecks67702G17
public import Erdos272.Arithmetic.N67702.SourceAtlasChecks67702G18
public import Erdos272.Arithmetic.N67702.SourceAtlasChecks67702G19
public import Erdos272.Arithmetic.N67702.SourceAtlasChecks67702G2
public import Erdos272.Arithmetic.N67702.SourceAtlasChecks67702G3
public import Erdos272.Arithmetic.N67702.SourceAtlasChecks67702G4
public import Erdos272.Arithmetic.N67702.SourceAtlasChecks67702G5
public import Erdos272.Arithmetic.N67702.SourceAtlasChecks67702G6
public import Erdos272.Arithmetic.N67702.SourceAtlasChecks67702G7
public import Erdos272.Arithmetic.N67702.SourceAtlasChecks67702G8
public import Erdos272.Arithmetic.N67702.SourceAtlasChecks67702G9

@[expose] public section

namespace JSP233.SourceAtlas67702
open StarCompletion SourceBridge208 IntrinsicTriples208 SourceContract86412
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option maxRecDepth 200000

abbrev demand := SourceAtlasData67702.demand
abbrev sourceReference := SourceAtlasData67702.sourceReference

theorem reference_eq {i : ℕ} (hi : i < 311) : (sourceReference i).contract=demand i := by
  by_cases h0 : i < 16
  · exact SourceAtlasChecks67702G0.reference_piece (by omega) h0
  by_cases h1 : i < 32
  · exact SourceAtlasChecks67702G1.reference_piece (by omega) h1
  by_cases h2 : i < 48
  · exact SourceAtlasChecks67702G2.reference_piece (by omega) h2
  by_cases h3 : i < 64
  · exact SourceAtlasChecks67702G3.reference_piece (by omega) h3
  by_cases h4 : i < 80
  · exact SourceAtlasChecks67702G4.reference_piece (by omega) h4
  by_cases h5 : i < 96
  · exact SourceAtlasChecks67702G5.reference_piece (by omega) h5
  by_cases h6 : i < 112
  · exact SourceAtlasChecks67702G6.reference_piece (by omega) h6
  by_cases h7 : i < 128
  · exact SourceAtlasChecks67702G7.reference_piece (by omega) h7
  by_cases h8 : i < 144
  · exact SourceAtlasChecks67702G8.reference_piece (by omega) h8
  by_cases h9 : i < 160
  · exact SourceAtlasChecks67702G9.reference_piece (by omega) h9
  by_cases h10 : i < 176
  · exact SourceAtlasChecks67702G10.reference_piece (by omega) h10
  by_cases h11 : i < 192
  · exact SourceAtlasChecks67702G11.reference_piece (by omega) h11
  by_cases h12 : i < 208
  · exact SourceAtlasChecks67702G12.reference_piece (by omega) h12
  by_cases h13 : i < 224
  · exact SourceAtlasChecks67702G13.reference_piece (by omega) h13
  by_cases h14 : i < 240
  · exact SourceAtlasChecks67702G14.reference_piece (by omega) h14
  by_cases h15 : i < 256
  · exact SourceAtlasChecks67702G15.reference_piece (by omega) h15
  by_cases h16 : i < 272
  · exact SourceAtlasChecks67702G16.reference_piece (by omega) h16
  by_cases h17 : i < 288
  · exact SourceAtlasChecks67702G17.reference_piece (by omega) h17
  by_cases h18 : i < 304
  · exact SourceAtlasChecks67702G18.reference_piece (by omega) h18
  exact SourceAtlasChecks67702G19.reference_piece (by omega) hi
#print axioms reference_eq

theorem actual_source {N i : ℕ} {S : Finset ℤ} (hi : i < 311)
    (hN : N ≤ 2^18) (hground : S ⊆ Ground N) (hS : 2 ≤ S.card)
    (hsize : (demand i).lower ≤ S.card) (hdefect : (demand i).defect ≤ Defect S) :
    (demand i).target ≤ (Pool S).card := by
  have hp : Paid (demand i) := by
    rw [← reference_eq hi]
    exact (sourceReference i).actual
  exact hp hN hground hS hsize hdefect
#print axioms actual_source
end
end JSP233.SourceAtlas67702
