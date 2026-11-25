module

public import Erdos272.Arithmetic.N80470.WitnessHighNumeric80470
public import Erdos272.Arithmetic.N80470.CleanupRows80470
public import Erdos272.Arithmetic.CleanupMachineSound208
public import Erdos272.Counting.N80470.WitnessActualFamily80470

@[expose] public section

namespace JSP233.WitnessHighSound80470
open scoped Classical BigOperators
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1000000

def toBand (b : WitnessHighNumeric80470.Band) : CleanupEval208.Band :=
  ⟨b.T,b.E,b.U,b.b2,b.b3,b.b5,b.b7,b.b11⟩
def row (k : ℕ) : CleanupEval208.Row := CleanupMachineSound208.toRow (CleanupRows80470.data k).row
def Witness (k : ℕ) : ℕ := (WitnessHighNumeric80470.data k).witness

theorem length {k : ℕ} (hk : k < 20) : (row k).bands.length=7 := by
  interval_cases k <;> rfl
#print axioms length

theorem links {k : ℕ} (hk : k < 20) :
    (WitnessHighNumeric80470.data k).high=(CleanupRows80470.data k).row.high ∧
    (WitnessHighNumeric80470.data k).steps=(CleanupRows80470.data k).steps ∧
    ∀ b : Fin 7, toBand (WitnessHighNumeric80470.band (WitnessHighNumeric80470.data k) b)=
      ActualCleanupEval208.At (row k) (length hk) b := by
  interval_cases k <;> refine ⟨rfl,rfl,?_⟩ <;> intro b <;> fin_cases b <;> rfl
#print axioms links

theorem block_eq (b : WitnessHighNumeric80470.Band) (d : ℕ) :
    WitnessHighNumeric80470.block b d=CleanupEval208.block (toBand b) d := by
  unfold WitnessHighNumeric80470.block CleanupEval208.block StepClass208.PrimeGate
  simp only [Nat.dvd_iff_mod_eq_zero]
  split_ifs <;> rfl
#print axioms block_eq

theorem cost_eq (N d W : ℕ) (b : WitnessHighNumeric80470.Band) :
    WitnessHighNumeric80470.cost N d b W=
      WitnessPieceBound80470.Bound N d (toBand b).T (toBand b).E
        (CleanupEval208.block (toBand b) d) (toBand b).U W := by
  unfold WitnessHighNumeric80470.cost
  rw [block_eq]
  rfl
#print axioms cost_eq

theorem high_value {k : ℕ} (hk : k < 20) :
    WitnessActualFamily80470.RowLight (row k) (length hk) (CleanupRows80470.data k).steps (Witness k)=
      WitnessHighNumeric80470.value (WitnessHighNumeric80470.data k) := by
  unfold WitnessActualFamily80470.RowLight WitnessHighNumeric80470.value
  rw [(links hk).1,(links hk).2.1]
  apply Finset.sum_congr rfl
  intro b hb
  rw [←(links hk).2.2 b]
  change (if (WitnessHighNumeric80470.band (WitnessHighNumeric80470.data k) b).E≤1 then 0 else _) = _
  by_cases he : (WitnessHighNumeric80470.band (WitnessHighNumeric80470.data k) b).E≤1
  · simp only [if_pos he]
  · simp only [if_neg he]
    apply Finset.sum_congr rfl
    intro d hd
    exact (cost_eq _ _ _ _).symm
#print axioms high_value
end
end JSP233.WitnessHighSound80470
