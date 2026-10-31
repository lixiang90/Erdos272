import Erdos272.Arithmetic.CleanupFast208
import Erdos272.Arithmetic.CleanupMachineSound208
import Erdos272.Arithmetic.WindowExtinction208

namespace JSP233.CleanupFastSound208
set_option maxHeartbeats 0

theorem machine_extinct {r : CleanupMachine208.Row} {d : ℕ} {b : CleanupMachine208.Band}
    (h : CleanupFast208.Extinct r d b) : CleanupMachine208.bandValue r d b=CleanupMachine208.bandZero := by
  rcases h with ⟨hlh,hET,hB,hTV,hsmall⟩
  let B:=CleanupMachine208.block b d
  let V:=b.U+B-3
  let A:=b.T-b.E
  let K:=V-b.E
  let J:=K-1
  let lo:=r.low/d
  let hi:=r.high/d
  have hLH : lo≤hi := Nat.div_le_div_right (c:=d) hlh
  have hAJ : A≤J := by dsimp [A,J,K,V];omega
  have hAK : A≤K := by omega
  have hzeroK : CleanupMachine208.Count hi K B=0 := by
    change LightClosed208.Count hi K B=0
    exact WindowExtinction208.count_zero (by omega : hi<K)
  have hzeroM : CleanupMachine208.maximum A J B lo hi=0 := by
    change WindowCounts208.maximum A J B lo hi=0
    exact WindowExtinction208.maximum_zero hLH hsmall
  have hzeroS : CleanupMachine208.maximum_sum A J B lo hi=0 := by
    change WindowSums208.maximum_sum A J B lo hi=0
    exact WindowExtinction208.maximum_sum_zero hB hAJ hsmall
  have hzeroC : CleanupMachine208.maximum_combined A K B ((V-1)/B+1) lo hi=0 := by
    change CombinedCounts208.maximum_combined A K B ((V-1)/B+1) lo hi=0
    exact WindowExtinction208.combined_zero hAK hLH hsmall
  have hzeroL : CleanupMachine208.Closed r.high d b.T b.E B V=0 := by
    change LightPrice208.Closed r.high d b.T b.E B V=0
    exact WindowExtinction208.closed_zero (by dsimp [V];omega : b.T≤V) hsmall
  dsimp only [B,V,A,K,J,lo,hi] at hzeroK hzeroM hzeroS hzeroC hzeroL
  by_cases hE : b.E≤1
  · simp only [CleanupMachine208.bandValue,if_pos hE]
  · simp only [CleanupMachine208.bandValue,if_neg hE,hzeroK,hzeroM,hzeroS,hzeroC,hzeroL,
      Nat.min_zero,Nat.lt_irrefl,if_false,Nat.zero_mul,Nat.zero_add,CleanupMachine208.bandZero]

theorem bandValue_eq (r : CleanupMachine208.Row) (d : ℕ) (b : CleanupMachine208.Band) :
    CleanupFast208.bandValue r d b=CleanupMachine208.bandValue r d b := by
  by_cases hE : b.E≤1
  · simp only [CleanupFast208.bandValue,CleanupMachine208.bandValue,if_pos hE]
  · by_cases he : CleanupFast208.Extinct r d b
    · rw [CleanupFast208.bandValue,if_neg hE,if_pos he,machine_extinct he]
    · rw [CleanupFast208.bandValue,if_neg hE,if_neg he]

theorem fold_eq (r : CleanupMachine208.Row) (d : ℕ) (bs : List CleanupMachine208.Band) :
    CleanupFast208.foldBands r d bs=CleanupMachine208.foldBands r d bs := by
  induction bs with
  | nil => rfl
  | cons b bs ih =>
    simp only [CleanupFast208.foldBands,CleanupMachine208.foldBands,bandValue_eq,ih]

theorem step_eq (r : CleanupMachine208.Row) (d : ℕ) :
    CleanupFast208.step r d=CleanupMachine208.step r d := by
  simp only [CleanupFast208.step,CleanupMachine208.step,fold_eq]

theorem run_eq (r : CleanupMachine208.Row) (start len : ℕ) :
    CleanupFast208.run r start len=CleanupMachine208.run r start len := by
  induction len with
  | zero => rfl
  | succ n ih => simp only [CleanupFast208.run,CleanupMachine208.run,ih,step_eq]

theorem check_sound {r : CleanupMachine208.Row} {start len : ℕ} {expected : CleanupMachine208.Totals}
    (h : CleanupFast208.checkChunk r start len expected=true) :
    CleanupEval208.ChunkFacts (CleanupMachineSound208.toRow r) start len (CleanupMachineSound208.toTotals expected) := by
  apply CleanupMachineSound208.check_sound
  simpa only [CleanupFast208.checkChunk,CleanupMachine208.checkChunk,run_eq] using h

#print axioms machine_extinct
#print axioms run_eq
#print axioms check_sound
end JSP233.CleanupFastSound208
