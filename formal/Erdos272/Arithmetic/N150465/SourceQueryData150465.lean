module

public import Erdos272.Resources.N158375.CorrelatedSource158375

@[expose] public section

namespace JSP233.SourceQueryData150465
open CorrelatedSource158375
noncomputable section
set_option maxRecDepth 200000
set_option maxHeartbeats 0

def queries : List Plan := [
  ⟨117, 1, 3732, 11⟩,
  ⟨117, 4, 14055, 21⟩,
  ⟨163, 2, 14055, 18⟩,
  ⟨224, 1, 14055, 15⟩,
  ⟨351, 1, 14055, 12⟩,
  ⟨585, 1, 14055, 9⟩,
  ⟨1170, 1, 14055, 7⟩,
  ⟨3744, 1, 14055, 4⟩,
  ⟨117, 11, 33624, 34⟩,
  ⟨163, 5, 33624, 28⟩,
  ⟨234, 3, 33624, 23⟩,
  ⟨350, 1, 33624, 18⟩,
  ⟨585, 1, 33624, 14⟩,
  ⟨1170, 1, 33624, 10⟩,
  ⟨3744, 1, 33624, 6⟩,
  ⟨117, 21, 52316, 44⟩,
  ⟨163, 8, 52316, 35⟩,
  ⟨234, 4, 52316, 28⟩,
  ⟨351, 2, 52316, 23⟩,
  ⟨434, 1, 52316, 21⟩,
  ⟨1170, 1, 52316, 12⟩,
  ⟨3744, 1, 52316, 7⟩,
  ⟨117, 32, 62162, 49⟩,
  ⟨163, 10, 62162, 39⟩,
  ⟨234, 5, 62162, 31⟩,
  ⟨351, 2, 62162, 25⟩,
  ⟨472, 1, 62162, 21⟩,
  ⟨1170, 1, 62162, 14⟩,
  ⟨3744, 1, 62162, 8⟩,
  ⟨117, 52, 68978, 52⟩,
  ⟨163, 11, 68978, 41⟩,
  ⟨234, 5, 68978, 33⟩,
  ⟨351, 3, 68978, 26⟩,
  ⟨496, 1, 68978, 22⟩,
  ⟨1170, 1, 68978, 14⟩,
  ⟨3744, 1, 68978, 8⟩,
  ⟨117, 56, 77306, 56⟩,
  ⟨163, 13, 77306, 44⟩,
  ⟨234, 6, 77306, 35⟩,
  ⟨351, 3, 77306, 28⟩,
  ⟨525, 1, 77306, 23⟩,
  ⟨1170, 1, 77306, 15⟩,
  ⟨3744, 1, 77306, 9⟩,
  ⟨117, 60, 85852, 60⟩,
  ⟨163, 15, 85852, 46⟩,
  ⟨234, 6, 85852, 37⟩,
  ⟨351, 3, 85852, 29⟩,
  ⟨552, 1, 85852, 23⟩,
  ⟨1170, 1, 85852, 16⟩,
  ⟨3744, 1, 85852, 9⟩,
  ⟨117, 64, 94956, 64⟩,
  ⟨163, 16, 94956, 49⟩,
  ⟨234, 7, 94956, 39⟩,
  ⟨351, 3, 94956, 31⟩,
  ⟨581, 1, 94956, 24⟩,
  ⟨1170, 1, 94956, 17⟩,
  ⟨3744, 1, 94956, 10⟩,
  ⟨117, 68, 105190, 68⟩,
  ⟨163, 19, 105190, 52⟩,
  ⟨234, 8, 105190, 41⟩,
  ⟨351, 4, 105190, 33⟩,
  ⟨585, 2, 105190, 25⟩,
  ⟨610, 1, 105190, 24⟩,
  ⟨3744, 1, 105190, 10⟩,
  ⟨117, 71, 113020, 71⟩,
  ⟨163, 21, 113020, 54⟩,
  ⟨234, 8, 113020, 43⟩,
  ⟨351, 4, 113020, 34⟩,
  ⟨585, 2, 113020, 26⟩,
  ⟨632, 1, 113020, 25⟩,
  ⟨3744, 1, 113020, 10⟩,
  ⟨117, 74, 121496, 74⟩,
  ⟨163, 23, 121496, 56⟩,
  ⟨234, 9, 121496, 44⟩,
  ⟨351, 4, 121496, 35⟩,
  ⟨585, 2, 121496, 27⟩,
  ⟨655, 1, 121496, 25⟩,
  ⟨3744, 1, 121496, 11⟩,
  ⟨117, 76, 127310, 76⟩,
  ⟨163, 25, 127310, 58⟩,
  ⟨234, 9, 127310, 45⟩,
  ⟨351, 4, 127310, 36⟩,
  ⟨585, 2, 127310, 27⟩,
  ⟨670, 1, 127310, 26⟩,
  ⟨3744, 1, 127310, 11⟩]

def query (i : ℕ) : Plan := (queries[i]?).getD ⟨0,0,0,0⟩

theorem checked0 : (List.range 16).all (fun j => decide (Conditions (query (0+j)))) = true := by decide +kernel
#print axioms checked0

theorem piece0 {i : ℕ} (hlo : 0 ≤ i) (hhi : i < 16) : Conditions (query i) := by
  have hm : i-0 ∈ List.range 16 := List.mem_range.mpr (by omega)
  have hc := of_decide_eq_true (List.all_eq_true.mp checked0 (i-0) hm)
  have he : 0+(i-0) = i := by omega
  simpa only [he] using hc
#print axioms piece0

theorem checked1 : (List.range 16).all (fun j => decide (Conditions (query (16+j)))) = true := by decide +kernel
#print axioms checked1

theorem piece1 {i : ℕ} (hlo : 16 ≤ i) (hhi : i < 32) : Conditions (query i) := by
  have hm : i-16 ∈ List.range 16 := List.mem_range.mpr (by omega)
  have hc := of_decide_eq_true (List.all_eq_true.mp checked1 (i-16) hm)
  have he : 16+(i-16) = i := by omega
  simpa only [he] using hc
#print axioms piece1

theorem checked2 : (List.range 16).all (fun j => decide (Conditions (query (32+j)))) = true := by decide +kernel
#print axioms checked2

theorem piece2 {i : ℕ} (hlo : 32 ≤ i) (hhi : i < 48) : Conditions (query i) := by
  have hm : i-32 ∈ List.range 16 := List.mem_range.mpr (by omega)
  have hc := of_decide_eq_true (List.all_eq_true.mp checked2 (i-32) hm)
  have he : 32+(i-32) = i := by omega
  simpa only [he] using hc
#print axioms piece2

theorem checked3 : (List.range 16).all (fun j => decide (Conditions (query (48+j)))) = true := by decide +kernel
#print axioms checked3

theorem piece3 {i : ℕ} (hlo : 48 ≤ i) (hhi : i < 64) : Conditions (query i) := by
  have hm : i-48 ∈ List.range 16 := List.mem_range.mpr (by omega)
  have hc := of_decide_eq_true (List.all_eq_true.mp checked3 (i-48) hm)
  have he : 48+(i-48) = i := by omega
  simpa only [he] using hc
#print axioms piece3

theorem checked4 : (List.range 16).all (fun j => decide (Conditions (query (64+j)))) = true := by decide +kernel
#print axioms checked4

theorem piece4 {i : ℕ} (hlo : 64 ≤ i) (hhi : i < 80) : Conditions (query i) := by
  have hm : i-64 ∈ List.range 16 := List.mem_range.mpr (by omega)
  have hc := of_decide_eq_true (List.all_eq_true.mp checked4 (i-64) hm)
  have he : 64+(i-64) = i := by omega
  simpa only [he] using hc
#print axioms piece4

theorem checked5 : (List.range 5).all (fun j => decide (Conditions (query (80+j)))) = true := by decide +kernel
#print axioms checked5

theorem piece5 {i : ℕ} (hlo : 80 ≤ i) (hhi : i < 85) : Conditions (query i) := by
  have hm : i-80 ∈ List.range 5 := List.mem_range.mpr (by omega)
  have hc := of_decide_eq_true (List.all_eq_true.mp checked5 (i-80) hm)
  have he : 80+(i-80) = i := by omega
  simpa only [he] using hc
#print axioms piece5

theorem conditions {i : ℕ} (hi : i < 85) : Conditions (query i) := by
  by_cases h0 : i < 16
  · exact piece0 (by omega) h0
  by_cases h1 : i < 32
  · exact piece1 (by omega) h1
  by_cases h2 : i < 48
  · exact piece2 (by omega) h2
  by_cases h3 : i < 64
  · exact piece3 (by omega) h3
  by_cases h4 : i < 80
  · exact piece4 (by omega) h4
  exact piece5 (by omega) hi
#print axioms conditions
end
end JSP233.SourceQueryData150465
