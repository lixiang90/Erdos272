module

public import Erdos272.Arithmetic.N67702.RowGeometry67702
public import Erdos272.Arithmetic.N67702.WitnessHighNumeric67702
public import Erdos272.Counting.N80470.WitnessHighSound80470

@[expose] public section

namespace JSP233.WitnessHighSoundData67702
open CleanupMachineSound208
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option maxRecDepth 200000

abbrev toBand := WitnessHighSound80470.toBand
def row (k : ℕ) : CleanupEval208.Row := toRow (CleanupRows67702.data k).row
def Witness (k : ℕ) : ℕ := (WitnessHighNumeric67702.data k).witness

theorem length {k : ℕ} (hk : k < 148) : (row k).bands.length=7 := by
  simpa only [row,toRow,List.length_map] using (RowGeometry67702.parameters hk).length
#print axioms length

def Links (k : ℕ) (hk : k < 148) : Prop :=
    (WitnessHighNumeric67702.data k).high=(CleanupRows67702.data k).row.high ∧
    (WitnessHighNumeric67702.data k).steps=(CleanupRows67702.data k).steps ∧
    ∀ b : Fin 7, toBand (WitnessHighNumeric80470.band (WitnessHighNumeric67702.data k) b)=
      ActualCleanupEval208.At (row k) (length hk) b

end
end JSP233.WitnessHighSoundData67702
