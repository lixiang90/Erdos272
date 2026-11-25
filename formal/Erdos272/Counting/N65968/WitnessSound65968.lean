module

public import Erdos272.Counting.N65968.FullSurplusFamily65968
public import Erdos272.Arithmetic.N65968.RowGeometry65968
public import Erdos272.Counting.N80470.WitnessHighSound80470
public import Erdos272.Arithmetic.N65968.WitnessNumeric65968

@[expose] public section

namespace JSP233.WitnessSound65968
open CleanupMachineSound208
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option maxRecDepth 200000

abbrev toBand := WitnessHighSound80470.toBand
def row (k : ℕ) : CleanupEval208.Row := toRow (CleanupRows65968.data k).row
def Witness (k : ℕ) : ℕ := (WitnessNumeric65968.data k).witness

theorem length {k : ℕ} (hk : k<128) : (row k).bands.length=7 := by
  simpa only [row,toRow,List.length_map] using (RowGeometry65968.parameters hk).length
#print axioms length

theorem links {k : ℕ} (hk : k<128) :
    (WitnessNumeric65968.data k).high=(CleanupRows65968.data k).row.high ∧
    (WitnessNumeric65968.data k).steps=(CleanupRows65968.data k).steps ∧
    ∀ b : Fin 7, toBand (WitnessNumeric65968.band (WitnessNumeric65968.data k) b)=
      ActualCleanupEval208.At (row k) (length hk) b := by
  interval_cases k <;> refine ⟨rfl,rfl,?_⟩ <;> intro b <;> fin_cases b <;> rfl
#print axioms links

theorem full_cost_eq (N d W : ℕ) (b : WitnessNumeric65968.Band) :
    WitnessNumeric65968.fullBound N d b.T b.E (WitnessNumeric65968.block b d) b.U W=
    FullSurplusActual65968.Bound N d (toBand b).T (toBand b).E
      (CleanupEval208.block (toBand b) d) (toBand b).U W := by
  simp only [WitnessNumeric65968.block,WitnessHighSound80470.block_eq]
  rfl
#print axioms full_cost_eq

theorem full_high_value {k : ℕ} (hk : k<128) :
    FullSurplusFamily65968.RowLight (row k) (length hk) (CleanupRows65968.data k).steps (Witness k)=
      WitnessNumeric65968.fullValue (WitnessNumeric65968.data k) := by
  unfold FullSurplusFamily65968.RowLight WitnessNumeric65968.fullValue
  rw [(links hk).1,(links hk).2.1]
  apply Finset.sum_congr rfl
  intro b hb
  rw [←(links hk).2.2 b]
  change (if (WitnessNumeric65968.band (WitnessNumeric65968.data k) b).E≤1 then 0 else _) = _
  by_cases he : (WitnessNumeric65968.band (WitnessNumeric65968.data k) b).E≤1
  · simp only [if_pos he]
  · simp only [if_neg he]
    apply Finset.sum_congr rfl
    intro d hd
    exact (full_cost_eq _ _ _ _).symm
#print axioms full_high_value

theorem legacy_high_value {k : ℕ} (hk : k<128) :
    WitnessActualFamily80470.RowLight (row k) (length hk) (CleanupRows65968.data k).steps (Witness k)=
      WitnessHighNumeric80470.value (WitnessNumeric65968.data k) := by
  unfold WitnessActualFamily80470.RowLight WitnessHighNumeric80470.value
  rw [(links hk).1,(links hk).2.1]
  apply Finset.sum_congr rfl
  intro b hb
  rw [←(links hk).2.2 b]
  change (if (WitnessNumeric65968.band (WitnessNumeric65968.data k) b).E≤1 then 0 else _) = _
  by_cases he : (WitnessNumeric65968.band (WitnessNumeric65968.data k) b).E≤1
  · simp only [if_pos he]
  · simp only [if_neg he]
    apply Finset.sum_congr rfl
    intro d hd
    exact (WitnessHighSound80470.cost_eq _ _ _ _).symm
#print axioms legacy_high_value

end
end JSP233.WitnessSound65968
