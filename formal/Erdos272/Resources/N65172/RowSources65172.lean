module

public import Erdos272.Resources.N65172.SourceAtlas65172
public import Erdos272.Resources.N67702.RowSources67702
public import Erdos272.Arithmetic.N65172.RowGeometry65172

@[expose] public section

namespace JSP233.RowSources65172
open StarCompletion SourceBridge208 IntrinsicTriples208 CleanupRows65172 UnitRecipeStatic208
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option maxRecDepth 200000

def queryIndex (k : ℕ) (b : Fin 7) : ℕ :=
  match k with
  | 0 => (([1, 27, 28, 29, 30, 31, 32] : List ℕ)[b.val]?).getD 0
  | 1 => (([2, 40, 41, 42, 43, 44, 45] : List ℕ)[b.val]?).getD 0
  | 2 => (([3, 46, 47, 48, 49, 50, 51] : List ℕ)[b.val]?).getD 0
  | 3 => (([5, 58, 59, 60, 61, 62, 63] : List ℕ)[b.val]?).getD 0
  | 4 => (([6, 64, 65, 66, 67, 68, 69] : List ℕ)[b.val]?).getD 0
  | 5 => (([8, 75, 76, 77, 78, 79, 80] : List ℕ)[b.val]?).getD 0
  | 6 => (([9, 81, 82, 83, 84, 85, 86] : List ℕ)[b.val]?).getD 0
  | 7 => (([10, 87, 88, 89, 90, 91, 92] : List ℕ)[b.val]?).getD 0
  | 8 => (([11, 38, 93, 94, 95, 96, 97] : List ℕ)[b.val]?).getD 0
  | 9 => (([12, 38, 98, 99, 100, 101, 102] : List ℕ)[b.val]?).getD 0
  | 10 => (([13, 38, 103, 104, 105, 106, 107] : List ℕ)[b.val]?).getD 0
  | 11 => (([14, 33, 108, 109, 110, 111, 112] : List ℕ)[b.val]?).getD 0
  | 12 => (([15, 33, 113, 114, 115, 116, 117] : List ℕ)[b.val]?).getD 0
  | 13 => (([16, 34, 118, 119, 120, 121, 122] : List ℕ)[b.val]?).getD 0
  | 14 => (([17, 34, 123, 124, 125, 126, 127] : List ℕ)[b.val]?).getD 0
  | 15 => (([18, 35, 128, 129, 130, 131, 132] : List ℕ)[b.val]?).getD 0
  | 16 => (([19, 35, 133, 134, 135, 136, 137] : List ℕ)[b.val]?).getD 0
  | 17 => (([20, 35, 138, 139, 140, 141, 142] : List ℕ)[b.val]?).getD 0
  | 18 => (([21, 35, 142, 143, 144, 145, 146] : List ℕ)[b.val]?).getD 0
  | 19 => (([22, 36, 147, 148, 149, 150, 151] : List ℕ)[b.val]?).getD 0
  | 20 => (([23, 36, 152, 153, 154, 155, 156] : List ℕ)[b.val]?).getD 0
  | 21 => (([24, 36, 157, 158, 159, 160, 161] : List ℕ)[b.val]?).getD 0
  | 22 => (([25, 37, 161, 162, 163, 164, 165] : List ℕ)[b.val]?).getD 0
  | 23 => (([26, 39, 166, 167, 168, 169, 170] : List ℕ)[b.val]?).getD 0
  | 24 => (([2, 40, 41, 42, 43, 44, 45] : List ℕ)[b.val]?).getD 0
  | 25 => (([4, 52, 53, 54, 55, 56, 57] : List ℕ)[b.val]?).getD 0
  | 26 => (([7, 69, 70, 71, 72, 73, 74] : List ℕ)[b.val]?).getD 0
  | 27 => (([9, 81, 82, 83, 84, 85, 86] : List ℕ)[b.val]?).getD 0
  | 28 => (([11, 38, 93, 94, 95, 96, 97] : List ℕ)[b.val]?).getD 0
  | 29 => (([13, 38, 103, 104, 105, 106, 107] : List ℕ)[b.val]?).getD 0
  | 30 => (([15, 33, 113, 114, 115, 116, 117] : List ℕ)[b.val]?).getD 0
  | 31 => (([17, 34, 123, 124, 125, 126, 127] : List ℕ)[b.val]?).getD 0
  | 32 => (([18, 35, 128, 129, 130, 131, 132] : List ℕ)[b.val]?).getD 0
  | 33 => (([19, 35, 133, 134, 135, 136, 137] : List ℕ)[b.val]?).getD 0
  | 34 => (([21, 35, 142, 143, 144, 145, 146] : List ℕ)[b.val]?).getD 0
  | 35 => (([23, 36, 152, 153, 154, 155, 156] : List ℕ)[b.val]?).getD 0
  | 36 => (([25, 37, 161, 162, 163, 164, 165] : List ℕ)[b.val]?).getD 0
  | _ => 0

def parentIndex (k : ℕ) : ℕ :=
  match k with
  | 37 => 140
  | 38 => 141
  | 39 => 142
  | 40 => 143
  | 41 => 144
  | 42 => 145
  | _ => 0

def NewLinks (k : ℕ) (b : Fin 7) : Prop :=
  queryIndex k b<171 ∧
  (SourceAtlas65172.demand (queryIndex k b)).lower≤(evalData (data k).row b).T ∧
  (SourceAtlas65172.demand (queryIndex k b)).defect≤(evalData (data k).row b).E ∧
  (data k).potential≤(SourceAtlas65172.demand (queryIndex k b)).target

instance (k : ℕ) (b : Fin 7) : Decidable (NewLinks k b) := by unfold NewLinks; infer_instance

def LegacyLinks (k : ℕ) (b : Fin 7) : Prop :=
  parentIndex k<148 ∧
  (data k).potential=(CleanupRows67702.data (parentIndex k)).potential ∧
  (evalData (CleanupRows67702.data (parentIndex k)).row b).T=(evalData (data k).row b).T ∧
  (evalData (CleanupRows67702.data (parentIndex k)).row b).E=(evalData (data k).row b).E

instance (k : ℕ) (b : Fin 7) : Decidable (LegacyLinks k b) := by unfold LegacyLinks; infer_instance

theorem all_new_links : ∀ k∈Finset.range 37, ∀ b : Fin 7, NewLinks k b := by decide +kernel
#print axioms all_new_links

theorem all_legacy_links : ∀ k∈Finset.Ico 37 43, ∀ b : Fin 7, LegacyLinks k b := by decide +kernel
#print axioms all_legacy_links

theorem actual_source {N k : ℕ} {S : Finset ℤ} (hk : k<43) (b : Fin 7)
    (hN : N≤2^18) (hground : S⊆Ground N) (hS : 2≤S.card)
    (hsize : (evalData (data k).row b).T≤S.card)
    (hdefect : (evalData (data k).row b).E≤Defect S) :
    (data k).potential≤(Pool S).card := by
  by_cases hnew : k<37
  · have hl:=all_new_links k (Finset.mem_range.mpr hnew) b
    exact hl.2.2.2.trans (SourceAtlas65172.actual_source hl.1 hN hground hS
      (hl.2.1.trans hsize) (hl.2.2.1.trans hdefect))
  · have hl:=all_legacy_links k (Finset.mem_Ico.mpr ⟨by omega,hk⟩) b
    have hp:=RowSources67702.actual_source hl.1 b hN hground hS
      (by rw [hl.2.2.1];exact hsize) (by rw [hl.2.2.2];exact hdefect)
    rw [hl.2.1]
    exact hp
#print axioms actual_source
end
end JSP233.RowSources65172
