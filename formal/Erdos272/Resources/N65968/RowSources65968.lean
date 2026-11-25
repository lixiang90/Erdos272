module

public import Erdos272.Resources.N65968.SourceAtlas65968
public import Erdos272.Resources.N67702.RowSources67702
public import Erdos272.Arithmetic.N65968.RowGeometry65968

@[expose] public section

namespace JSP233.RowSources65968
open StarCompletion SourceBridge208 IntrinsicTriples208 CleanupRows65968 UnitRecipeStatic208
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option maxRecDepth 200000

def queryIndex (k : ℕ) (b : Fin 7) : ℕ :=
  match k with
  | 0 => (([2, 45, 46, 47, 48, 49, 50] : List ℕ)[b.val]?).getD 0
  | 1 => (([4, 59, 60, 61, 62, 63, 64] : List ℕ)[b.val]?).getD 0
  | 2 => (([6, 71, 72, 73, 74, 75, 76] : List ℕ)[b.val]?).getD 0
  | 3 => (([8, 83, 84, 85, 86, 87, 88] : List ℕ)[b.val]?).getD 0
  | 4 => (([10, 95, 96, 97, 98, 99, 100] : List ℕ)[b.val]?).getD 0
  | 5 => (([11, 101, 102, 103, 104, 105, 106] : List ℕ)[b.val]?).getD 0
  | 6 => (([12, 107, 108, 109, 110, 111, 112] : List ℕ)[b.val]?).getD 0
  | 7 => (([15, 51, 124, 125, 126, 127, 128] : List ℕ)[b.val]?).getD 0
  | 8 => (([17, 51, 134, 135, 136, 137, 138] : List ℕ)[b.val]?).getD 0
  | 9 => (([19, 40, 144, 145, 146, 147, 148] : List ℕ)[b.val]?).getD 0
  | 10 => (([21, 41, 151, 152, 153, 154, 155] : List ℕ)[b.val]?).getD 0
  | 11 => (([22, 41, 156, 157, 158, 159, 160] : List ℕ)[b.val]?).getD 0
  | 12 => (([24, 42, 163, 164, 165, 166, 167] : List ℕ)[b.val]?).getD 0
  | 13 => (([26, 42, 171, 172, 173, 174, 175] : List ℕ)[b.val]?).getD 0
  | 14 => (([28, 42, 180, 181, 182, 183, 184] : List ℕ)[b.val]?).getD 0
  | 15 => (([29, 43, 185, 186, 187, 188, 189] : List ℕ)[b.val]?).getD 0
  | 16 => (([30, 43, 190, 191, 192, 193, 194] : List ℕ)[b.val]?).getD 0
  | 17 => (([31, 43, 195, 196, 197, 198, 199] : List ℕ)[b.val]?).getD 0
  | 18 => (([32, 44, 199, 200, 201, 202, 203] : List ℕ)[b.val]?).getD 0
  | 19 => (([33, 52, 204, 205, 206, 207, 208] : List ℕ)[b.val]?).getD 0
  | 20 => (([1, 34, 35, 36, 37, 38, 39] : List ℕ)[b.val]?).getD 0
  | 21 => (([2, 45, 46, 47, 48, 49, 50] : List ℕ)[b.val]?).getD 0
  | 22 => (([3, 53, 54, 55, 56, 57, 58] : List ℕ)[b.val]?).getD 0
  | 23 => (([5, 65, 66, 67, 68, 69, 70] : List ℕ)[b.val]?).getD 0
  | 24 => (([6, 71, 72, 73, 74, 75, 76] : List ℕ)[b.val]?).getD 0
  | 25 => (([7, 77, 78, 79, 80, 81, 82] : List ℕ)[b.val]?).getD 0
  | 26 => (([8, 83, 84, 85, 86, 87, 88] : List ℕ)[b.val]?).getD 0
  | 27 => (([9, 89, 90, 91, 92, 93, 94] : List ℕ)[b.val]?).getD 0
  | 28 => (([10, 95, 96, 97, 98, 99, 100] : List ℕ)[b.val]?).getD 0
  | 29 => (([11, 101, 102, 103, 104, 105, 106] : List ℕ)[b.val]?).getD 0
  | 30 => (([12, 107, 108, 109, 110, 111, 112] : List ℕ)[b.val]?).getD 0
  | 31 => (([13, 113, 114, 115, 116, 117, 118] : List ℕ)[b.val]?).getD 0
  | 32 => (([14, 51, 119, 120, 121, 122, 123] : List ℕ)[b.val]?).getD 0
  | 33 => (([15, 51, 124, 125, 126, 127, 128] : List ℕ)[b.val]?).getD 0
  | 34 => (([16, 51, 129, 130, 131, 132, 133] : List ℕ)[b.val]?).getD 0
  | 35 => (([17, 51, 134, 135, 136, 137, 138] : List ℕ)[b.val]?).getD 0
  | 36 => (([18, 40, 139, 140, 141, 142, 143] : List ℕ)[b.val]?).getD 0
  | 37 => (([19, 40, 144, 145, 146, 147, 148] : List ℕ)[b.val]?).getD 0
  | 38 => (([20, 40, 146, 147, 148, 149, 150] : List ℕ)[b.val]?).getD 0
  | 39 => (([21, 41, 151, 152, 153, 154, 155] : List ℕ)[b.val]?).getD 0
  | 40 => (([22, 41, 156, 157, 158, 159, 160] : List ℕ)[b.val]?).getD 0
  | 41 => (([23, 41, 158, 159, 160, 161, 162] : List ℕ)[b.val]?).getD 0
  | 42 => (([24, 42, 163, 164, 165, 166, 167] : List ℕ)[b.val]?).getD 0
  | 43 => (([25, 42, 166, 167, 168, 169, 170] : List ℕ)[b.val]?).getD 0
  | 44 => (([26, 42, 171, 172, 173, 174, 175] : List ℕ)[b.val]?).getD 0
  | 45 => (([27, 42, 176, 177, 178, 179, 180] : List ℕ)[b.val]?).getD 0
  | 46 => (([28, 42, 180, 181, 182, 183, 184] : List ℕ)[b.val]?).getD 0
  | 47 => (([29, 43, 185, 186, 187, 188, 189] : List ℕ)[b.val]?).getD 0
  | 48 => (([30, 43, 190, 191, 192, 193, 194] : List ℕ)[b.val]?).getD 0
  | 49 => (([31, 43, 195, 196, 197, 198, 199] : List ℕ)[b.val]?).getD 0
  | 50 => (([32, 44, 199, 200, 201, 202, 203] : List ℕ)[b.val]?).getD 0
  | 51 => (([33, 52, 204, 205, 206, 207, 208] : List ℕ)[b.val]?).getD 0
  | _ => 0

def parentIndex (k : ℕ) : ℕ :=
  match k with
  | 52 => 0
  | 53 => 1
  | 54 => 2
  | 55 => 3
  | 56 => 4
  | 57 => 5
  | 58 => 6
  | 59 => 7
  | 60 => 8
  | 61 => 9
  | 62 => 10
  | 63 => 11
  | 64 => 12
  | 65 => 13
  | 66 => 14
  | 67 => 15
  | 68 => 16
  | 69 => 17
  | 70 => 18
  | 71 => 19
  | 72 => 20
  | 73 => 21
  | 74 => 22
  | 75 => 23
  | 76 => 24
  | 77 => 25
  | 78 => 26
  | 79 => 27
  | 80 => 28
  | 81 => 29
  | 82 => 30
  | 83 => 31
  | 84 => 32
  | 85 => 33
  | 86 => 34
  | 87 => 35
  | 88 => 36
  | 89 => 37
  | 90 => 38
  | 91 => 39
  | 92 => 40
  | 93 => 41
  | 94 => 42
  | 95 => 43
  | 96 => 44
  | 97 => 45
  | 98 => 46
  | 99 => 47
  | 100 => 48
  | 101 => 49
  | 102 => 50
  | 103 => 51
  | 104 => 52
  | 105 => 53
  | 106 => 54
  | 107 => 55
  | 108 => 56
  | 109 => 57
  | 110 => 58
  | 111 => 59
  | 112 => 60
  | 113 => 61
  | 114 => 62
  | 115 => 63
  | 116 => 116
  | 117 => 117
  | 118 => 118
  | 119 => 119
  | 120 => 120
  | 121 => 121
  | 122 => 122
  | 123 => 123
  | 124 => 124
  | 125 => 125
  | 126 => 126
  | 127 => 127
  | _ => 0

def NewLinks (k : ℕ) (b : Fin 7) : Prop :=
  queryIndex k b<209 ∧
  (SourceAtlas65968.demand (queryIndex k b)).lower≤(evalData (data k).row b).T ∧
  (SourceAtlas65968.demand (queryIndex k b)).defect≤(evalData (data k).row b).E ∧
  (data k).potential≤(SourceAtlas65968.demand (queryIndex k b)).target

instance (k : ℕ) (b : Fin 7) : Decidable (NewLinks k b) := by unfold NewLinks; infer_instance

def LegacyLinks (k : ℕ) (b : Fin 7) : Prop :=
  parentIndex k<148 ∧
  (data k).potential=(CleanupRows67702.data (parentIndex k)).potential ∧
  (evalData (CleanupRows67702.data (parentIndex k)).row b).T=(evalData (data k).row b).T ∧
  (evalData (CleanupRows67702.data (parentIndex k)).row b).E=(evalData (data k).row b).E

instance (k : ℕ) (b : Fin 7) : Decidable (LegacyLinks k b) := by unfold LegacyLinks; infer_instance

theorem all_new_links : ∀ k∈Finset.range 52, ∀ b : Fin 7, NewLinks k b := by decide +kernel
#print axioms all_new_links

theorem all_legacy_links : ∀ k∈Finset.Ico 52 128, ∀ b : Fin 7, LegacyLinks k b := by decide +kernel
#print axioms all_legacy_links

theorem actual_source {N k : ℕ} {S : Finset ℤ} (hk : k<128) (b : Fin 7)
    (hN : N≤2^18) (hground : S⊆Ground N) (hS : 2≤S.card)
    (hsize : (evalData (data k).row b).T≤S.card)
    (hdefect : (evalData (data k).row b).E≤Defect S) :
    (data k).potential≤(Pool S).card := by
  by_cases hnew : k<52
  · have hl:=all_new_links k (Finset.mem_range.mpr hnew) b
    exact hl.2.2.2.trans (SourceAtlas65968.actual_source hl.1 hN hground hS
      (hl.2.1.trans hsize) (hl.2.2.1.trans hdefect))
  · have hl:=all_legacy_links k (Finset.mem_Ico.mpr ⟨by omega,hk⟩) b
    have hp:=RowSources67702.actual_source hl.1 b hN hground hS
      (by rw [hl.2.2.1];exact hsize) (by rw [hl.2.2.2];exact hdefect)
    rw [hl.2.1]
    exact hp
#print axioms actual_source
end
end JSP233.RowSources65968
