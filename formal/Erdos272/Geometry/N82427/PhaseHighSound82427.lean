module

public import Erdos272.Geometry.N82427.PhaseSlope82427
public import Erdos272.Geometry.N82427.PhaseNumeric82427
public import Erdos272.Arithmetic.N82427.CleanupRows82427
public import Erdos272.Arithmetic.CleanupMachineSound208

@[expose] public section

namespace JSP233.PhaseHighSound82427
open scoped Classical BigOperators
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1000000

def toBand (b : PhaseNumeric82427.Band) : CleanupEval208.Band :=
  ⟨b.T,b.E,b.U,b.b2,b.b3,b.b5,b.b7,b.b11⟩

def row (k : ℕ) : CleanupEval208.Row :=
  CleanupMachineSound208.toRow (CleanupRows82427.data k).row

theorem length {k : ℕ} (hk : k < 88) : (row k).bands.length=7 := by
  interval_cases k <;> rfl

theorem links {k : ℕ} (hk : k < 88) :
    (PhaseNumeric82427.data k).high=(CleanupRows82427.data k).row.high ∧
    (PhaseNumeric82427.data k).steps=(CleanupRows82427.data k).steps ∧
    ∀ b : Fin 7, toBand (PhaseNumeric82427.band (PhaseNumeric82427.data k) b)=
      ActualCleanupEval208.At (row k) (length hk) b := by
  interval_cases k <;> refine ⟨rfl,rfl,?_⟩ <;> intro b <;> fin_cases b <;> rfl

theorem shapes {k : ℕ} (hk : k < 88) (b : Fin 7) :
    let t := PhaseNumeric82427.band (PhaseNumeric82427.data k) b
    t.E<t.T ∧ t.T<t.U ∧ 3≤t.b2 ∧ 3≤t.b3 ∧ 3≤t.b5 ∧ 3≤t.b7 ∧ 3≤t.b11 := by
  interval_cases k <;> fin_cases b <;> decide +kernel

theorem block_eq (b : PhaseNumeric82427.Band) (d : ℕ) :
    PhaseNumeric82427.block b d=CleanupEval208.block (toBand b) d := by
  unfold PhaseNumeric82427.block CleanupEval208.block StepClass208.PrimeGate
  split_ifs <;> rfl

theorem closed_eq (N d T E B V : ℕ) :
    PhaseNumeric82427.Closed N d T E B V=PhaseClosed82427.Closed N d T E B V := rfl

theorem block_three {k : ℕ} (hk : k < 88) (b : Fin 7) (d : ℕ) :
    3 ≤ CleanupEval208.block (ActualCleanupEval208.At (row k) (length hk) b) d := by
  rw [←(links hk).2.2 b,←block_eq]
  have hs := shapes hk b
  unfold PhaseNumeric82427.block
  split_ifs <;> omega

theorem cost_eq {N d : ℕ} {b : PhaseNumeric82427.Band} (hd : 0<d)
    (hET : b.E<b.T) (hshape : PhaseSlope82427.Shape (toBand b)) :
    PhaseNumeric82427.cost N d b=PhaseSlope82427.BandCost N d (toBand b) := by
  obtain ⟨hB,_hE,hTV⟩ := PhaseSlope82427.shape_block hshape d
  unfold PhaseNumeric82427.cost PhaseSlope82427.BandCost
  change (if b.E≤1 then 0 else _)=(if b.E≤1 then 0 else _)
  by_cases he : b.E≤1
  · simp only [if_pos he]
  · simp only [if_neg he]
    rw [block_eq,closed_eq]
    exact (PhaseClosed82427.price_closed hd hB hET hTV).symm

theorem high_value {k : ℕ} (hk : k < 88) :
    PhaseSlope82427.RowLight (row k) (length hk) (CleanupRows82427.data k).steps
      (CleanupRows82427.data k).row.high = PhaseNumeric82427.value (PhaseNumeric82427.data k) := by
  have hv : PhaseNumeric82427.value (PhaseNumeric82427.data k) =
      ∑ d ∈ Finset.Icc 1 (PhaseNumeric82427.data k).steps, ∑ b : Fin 7,
        PhaseNumeric82427.cost (PhaseNumeric82427.data k).high d
          (PhaseNumeric82427.band (PhaseNumeric82427.data k) b) := by
    unfold PhaseNumeric82427.value
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro b hb
    split_ifs with he
    · symm
      apply Finset.sum_eq_zero
      intro d hd
      exact if_pos he
    · rfl
  rw [hv]
  unfold PhaseSlope82427.RowLight
  rw [(links hk).1,(links hk).2.1]
  apply Finset.sum_congr rfl
  intro d hd
  apply Finset.sum_congr rfl
  intro b _hb
  have hs := shapes hk b
  have hshape : PhaseSlope82427.Shape (toBand (PhaseNumeric82427.band (PhaseNumeric82427.data k) b)) :=
    ⟨hs.1.le,hs.2.1,by dsimp only [toBand]; omega,by dsimp only [toBand]; omega,
      by dsimp only [toBand]; omega,by dsimp only [toBand]; omega,by dsimp only [toBand]; omega⟩
  rw [cost_eq (by have hh := (Finset.mem_Icc.mp hd).1; omega) hs.1 hshape,(links hk).2.2 b]

#print axioms length
#print axioms links
#print axioms shapes
#print axioms block_eq
#print axioms closed_eq
#print axioms block_three
#print axioms cost_eq
#print axioms high_value
end
end JSP233.PhaseHighSound82427
