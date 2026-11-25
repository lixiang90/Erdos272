module

public import Erdos272.Arithmetic.N67702.RowSourceChecks67702G0
public import Erdos272.Arithmetic.N67702.RowSourceChecks67702G1
public import Erdos272.Arithmetic.N67702.RowSourceChecks67702G2
public import Erdos272.Arithmetic.N67702.RowSourceChecks67702G3
public import Erdos272.Arithmetic.N67702.RowSourceChecks67702G4
public import Erdos272.Arithmetic.N67702.RowSourceChecks67702G5
public import Erdos272.Arithmetic.N67702.RowSourceChecks67702G6
public import Erdos272.Arithmetic.N67702.RowSourceChecks67702G7
public import Erdos272.Arithmetic.N67702.RowSourceChecks67702G8
public import Erdos272.Arithmetic.N67702.RowSourceChecks67702G9

@[expose] public section

namespace JSP233.RowSources67702
open StarCompletion SourceBridge208 IntrinsicTriples208 CleanupRows67702 UnitRecipeStatic208 RowSourceData67702
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option maxRecDepth 200000

theorem links {k : ℕ} (hk : k < 148) (b : Fin 7) : Links k b := by
  by_cases h0 : k < 16
  · exact RowSourceChecks67702G0.links (by omega) h0 b
  by_cases h1 : k < 32
  · exact RowSourceChecks67702G1.links (by omega) h1 b
  by_cases h2 : k < 48
  · exact RowSourceChecks67702G2.links (by omega) h2 b
  by_cases h3 : k < 64
  · exact RowSourceChecks67702G3.links (by omega) h3 b
  by_cases h4 : k < 80
  · exact RowSourceChecks67702G4.links (by omega) h4 b
  by_cases h5 : k < 96
  · exact RowSourceChecks67702G5.links (by omega) h5 b
  by_cases h6 : k < 112
  · exact RowSourceChecks67702G6.links (by omega) h6 b
  by_cases h7 : k < 128
  · exact RowSourceChecks67702G7.links (by omega) h7 b
  by_cases h8 : k < 144
  · exact RowSourceChecks67702G8.links (by omega) h8 b
  exact RowSourceChecks67702G9.links (by omega) hk b
#print axioms links

theorem actual_source {N k : ℕ} {S : Finset ℤ} (hk : k < 148) (b : Fin 7)
    (hN : N ≤ 2^18) (hground : S ⊆ Ground N) (hS : 2 ≤ S.card)
    (hsize : (evalData (data k).row b).T ≤ S.card)
    (hdefect : (evalData (data k).row b).E ≤ Defect S) :
    (data k).potential ≤ (Pool S).card := by
  have hl := links hk b
  have hb := SourceAtlas67702.actual_source hl.1 hN hground hS
    (hl.2.1.trans hsize) (hl.2.2.1.trans hdefect)
  exact hl.2.2.2.trans hb
#print axioms actual_source
end
end JSP233.RowSources67702
