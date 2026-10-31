import Erdos272.Arithmetic.CleanupMachine208
import Erdos272.Resources.CleanupChecked208

namespace JSP233.CleanupMachineSound208
set_option maxHeartbeats 0

def toBand (b : CleanupMachine208.Band) : CleanupEval208.Band :=
  ⟨b.T,b.E,b.U,b.b2,b.b3,b.b5,b.b7,b.b11⟩
def toRow (r : CleanupMachine208.Row) : CleanupEval208.Row :=
  ⟨r.grid,r.low,r.high,r.i,r.bands.map toBand⟩
def toTotals (t : CleanupMachine208.Totals) : CleanupEval208.Totals :=
  ⟨t.first,t.second,t.credit,t.net,t.light⟩
def toValue (v : CleanupMachine208.BandValue) : CleanupEval208.BandValue :=
  ⟨v.count,v.windows,v.credit,v.light⟩
def toFold (v : CleanupMachine208.BandFold) : CleanupEval208.BandFold := ⟨toValue v.value,v.good⟩
def toChunk (v : CleanupMachine208.Chunk) : CleanupEval208.Chunk := ⟨toTotals v.totals,v.good⟩

theorem bandValue_eq (r : CleanupMachine208.Row) (d : ℕ) (b : CleanupMachine208.Band) :
    toValue (CleanupMachine208.bandValue r d b)=CleanupEval208.bandValue (toRow r) d (toBand b) := by
  by_cases h : b.E≤1
  · have h' : (toBand b).E ≤ 1 := h
    simp only [CleanupMachine208.bandValue,CleanupEval208.bandValue,ite_eq_left h,ite_eq_left h']
    rfl
  · have h' : ¬ (toBand b).E ≤ 1 := h
    simp only [CleanupMachine208.bandValue,CleanupEval208.bandValue,ite_eq_right h,ite_eq_right h']
    rfl

theorem fold_eq (r : CleanupMachine208.Row) (d : ℕ) (bs : List CleanupMachine208.Band) :
    toFold (CleanupMachine208.foldBands r d bs)=CleanupEval208.foldBands (toRow r) d (bs.map toBand) := by
  induction bs with
  | nil => rfl
  | cons b bs ih =>
    change (⟨CleanupEval208.bandAdd (toValue (CleanupMachine208.bandValue r d b))
        (toFold (CleanupMachine208.foldBands r d bs)).value,
      decide (CleanupEval208.BandGood (toRow r) d (toBand b) (toValue (CleanupMachine208.bandValue r d b))) &&
        (toFold (CleanupMachine208.foldBands r d bs)).good⟩ : CleanupEval208.BandFold)=_
    rw [bandValue_eq,ih]
    rfl

theorem step_eq (r : CleanupMachine208.Row) (d : ℕ) :
    toChunk (CleanupMachine208.step r d)=CleanupEval208.step (toRow r) d := by
  change (⟨⟨(toFold (CleanupMachine208.foldBands r d r.bands)).value.count*
      min r.grid (toFold (CleanupMachine208.foldBands r d r.bands)).value.windows,
    (toFold (CleanupMachine208.foldBands r d r.bands)).value.count*CleanupNet208.Ceil (r.i*r.grid) r.low,
    (toFold (CleanupMachine208.foldBands r d r.bands)).value.credit,
    (toFold (CleanupMachine208.foldBands r d r.bands)).value.count*
        min r.grid (toFold (CleanupMachine208.foldBands r d r.bands)).value.windows+
      (toFold (CleanupMachine208.foldBands r d r.bands)).value.count*CleanupNet208.Ceil (r.i*r.grid) r.low-
        (toFold (CleanupMachine208.foldBands r d r.bands)).value.credit,
    (toFold (CleanupMachine208.foldBands r d r.bands)).value.light⟩,
    (toFold (CleanupMachine208.foldBands r d r.bands)).good &&
      decide (0<r.grid ∧ 0<r.low ∧ r.low≤r.high ∧ 0<d ∧
        (toFold (CleanupMachine208.foldBands r d r.bands)).value.credit≤
          (toFold (CleanupMachine208.foldBands r d r.bands)).value.count*
            min r.grid (toFold (CleanupMachine208.foldBands r d r.bands)).value.windows+
          (toFold (CleanupMachine208.foldBands r d r.bands)).value.count*CleanupNet208.Ceil (r.i*r.grid) r.low)⟩ : CleanupEval208.Chunk)=_
  rw [fold_eq]
  rfl

theorem run_eq (r : CleanupMachine208.Row) (start len : ℕ) :
    toChunk (CleanupMachine208.run r start len)=CleanupEval208.run (toRow r) start len := by
  induction len with
  | zero => rfl
  | succ n ih =>
    change (⟨CleanupEval208.add (toChunk (CleanupMachine208.run r start n)).totals
        (toChunk (CleanupMachine208.step r (start+n))).totals,
      (toChunk (CleanupMachine208.run r start n)).good &&
        (toChunk (CleanupMachine208.step r (start+n))).good⟩ : CleanupEval208.Chunk)=_
    rw [ih,step_eq]
    rfl

theorem check_sound {r : CleanupMachine208.Row} {start len : ℕ} {expected : CleanupMachine208.Totals}
    (h : CleanupMachine208.checkChunk r start len expected=true) :
    CleanupEval208.ChunkFacts (toRow r) start len (toTotals expected) := by
  have hm : (CleanupMachine208.run r start len).good=true ∧
      decide ((CleanupMachine208.run r start len).totals=expected)=true := by
    simpa only [CleanupMachine208.checkChunk,Bool.and_eq_true] using h
  have hmt : (CleanupMachine208.run r start len).totals=expected := of_decide_eq_true hm.2
  have hr := run_eq r start len
  have hg : (CleanupEval208.run (toRow r) start len).good=true := by
    rw [←hr]
    exact hm.1
  have ht : (CleanupEval208.run (toRow r) start len).totals=toTotals expected := by
    rw [←hr]
    exact congrArg toTotals hmt
  apply CleanupEval208.check_sound
  simp only [CleanupEval208.checkChunk,Bool.and_eq_true]
  exact ⟨hg,decide_eq_true ht⟩

#print axioms bandValue_eq
#print axioms run_eq
#print axioms check_sound
end JSP233.CleanupMachineSound208
