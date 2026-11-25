module

public import Erdos272.Arithmetic.N82427.RowGeometry82427
public import Erdos272.Resources.N82427.SourceAtlas82427

@[expose] public section

namespace JSP233.RowSources82427
open StarCompletion SourceBridge208 IntrinsicTriples208 CleanupRows82427 UnitRecipeStatic208
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option maxRecDepth 200000

def queryIndex (k : ℕ) (b : Fin 7) : ℕ :=
  match k with
  | 0 => (([1, 2, 2, 2, 2, 2, 2] : List ℕ)[b.val]?).getD 0
  | 1 => (([3, 4, 4, 4, 4, 4, 4] : List ℕ)[b.val]?).getD 0
  | 2 => (([5, 6, 6, 6, 6, 6, 6] : List ℕ)[b.val]?).getD 0
  | 3 => (([7, 8, 8, 8, 8, 8, 8] : List ℕ)[b.val]?).getD 0
  | 4 => (([9, 10, 10, 10, 10, 10, 10] : List ℕ)[b.val]?).getD 0
  | 5 => (([11, 12, 12, 12, 12, 12, 12] : List ℕ)[b.val]?).getD 0
  | 6 => (([13, 14, 14, 14, 14, 14, 14] : List ℕ)[b.val]?).getD 0
  | 7 => (([15, 16, 16, 16, 16, 16, 16] : List ℕ)[b.val]?).getD 0
  | 8 => (([17, 18, 18, 18, 18, 18, 18] : List ℕ)[b.val]?).getD 0
  | 9 => (([19, 20, 20, 20, 20, 20, 20] : List ℕ)[b.val]?).getD 0
  | 10 => (([21, 22, 22, 22, 22, 22, 22] : List ℕ)[b.val]?).getD 0
  | 11 => (([23, 24, 24, 24, 24, 24, 24] : List ℕ)[b.val]?).getD 0
  | 12 => (([25, 26, 26, 26, 26, 26, 26] : List ℕ)[b.val]?).getD 0
  | 13 => (([27, 28, 28, 28, 28, 28, 28] : List ℕ)[b.val]?).getD 0
  | 14 => (([29, 30, 31, 31, 31, 31, 31] : List ℕ)[b.val]?).getD 0
  | 15 => (([32, 33, 34, 34, 34, 34, 34] : List ℕ)[b.val]?).getD 0
  | 16 => (([35, 36, 37, 37, 37, 37, 37] : List ℕ)[b.val]?).getD 0
  | 17 => (([38, 39, 40, 40, 40, 40, 40] : List ℕ)[b.val]?).getD 0
  | 18 => (([41, 42, 43, 43, 43, 43, 43] : List ℕ)[b.val]?).getD 0
  | 19 => (([44, 45, 46, 46, 46, 46, 46] : List ℕ)[b.val]?).getD 0
  | 20 => (([47, 48, 49, 49, 49, 49, 49] : List ℕ)[b.val]?).getD 0
  | 21 => (([50, 51, 52, 52, 52, 52, 52] : List ℕ)[b.val]?).getD 0
  | 22 => (([53, 54, 55, 55, 55, 55, 55] : List ℕ)[b.val]?).getD 0
  | 23 => (([56, 57, 58, 58, 58, 58, 58] : List ℕ)[b.val]?).getD 0
  | 24 => (([59, 60, 61, 61, 61, 61, 61] : List ℕ)[b.val]?).getD 0
  | 25 => (([62, 63, 64, 64, 64, 64, 64] : List ℕ)[b.val]?).getD 0
  | 26 => (([65, 66, 67, 67, 67, 67, 67] : List ℕ)[b.val]?).getD 0
  | 27 => (([68, 69, 70, 70, 70, 70, 70] : List ℕ)[b.val]?).getD 0
  | 28 => (([71, 72, 73, 73, 73, 73, 73] : List ℕ)[b.val]?).getD 0
  | 29 => (([74, 75, 76, 76, 76, 76, 76] : List ℕ)[b.val]?).getD 0
  | 30 => (([77, 78, 79, 79, 79, 79, 79] : List ℕ)[b.val]?).getD 0
  | 31 => (([80, 81, 82, 82, 82, 82, 82] : List ℕ)[b.val]?).getD 0
  | 32 => (([83, 84, 85, 85, 85, 85, 85] : List ℕ)[b.val]?).getD 0
  | 33 => (([86, 87, 88, 88, 88, 88, 88] : List ℕ)[b.val]?).getD 0
  | 34 => (([89, 90, 91, 91, 91, 91, 91] : List ℕ)[b.val]?).getD 0
  | 35 => (([92, 93, 94, 94, 94, 94, 94] : List ℕ)[b.val]?).getD 0
  | 36 => (([1, 2, 2, 2, 2, 2, 2] : List ℕ)[b.val]?).getD 0
  | 37 => (([3, 4, 4, 4, 4, 4, 4] : List ℕ)[b.val]?).getD 0
  | 38 => (([5, 6, 6, 6, 6, 6, 6] : List ℕ)[b.val]?).getD 0
  | 39 => (([7, 8, 8, 8, 8, 8, 8] : List ℕ)[b.val]?).getD 0
  | 40 => (([95, 96, 96, 96, 96, 96, 96] : List ℕ)[b.val]?).getD 0
  | 41 => (([9, 10, 10, 10, 10, 10, 10] : List ℕ)[b.val]?).getD 0
  | 42 => (([11, 12, 12, 12, 12, 12, 12] : List ℕ)[b.val]?).getD 0
  | 43 => (([13, 14, 14, 14, 14, 14, 14] : List ℕ)[b.val]?).getD 0
  | 44 => (([15, 16, 16, 16, 16, 16, 16] : List ℕ)[b.val]?).getD 0
  | 45 => (([17, 18, 18, 18, 18, 18, 18] : List ℕ)[b.val]?).getD 0
  | 46 => (([19, 20, 20, 20, 20, 20, 20] : List ℕ)[b.val]?).getD 0
  | 47 => (([21, 22, 22, 22, 22, 22, 22] : List ℕ)[b.val]?).getD 0
  | 48 => (([23, 24, 24, 24, 24, 24, 24] : List ℕ)[b.val]?).getD 0
  | 49 => (([25, 26, 26, 26, 26, 26, 26] : List ℕ)[b.val]?).getD 0
  | 50 => (([27, 28, 28, 28, 28, 28, 28] : List ℕ)[b.val]?).getD 0
  | 51 => (([29, 30, 31, 31, 31, 31, 31] : List ℕ)[b.val]?).getD 0
  | 52 => (([32, 33, 34, 34, 34, 34, 34] : List ℕ)[b.val]?).getD 0
  | 53 => (([35, 36, 37, 37, 37, 37, 37] : List ℕ)[b.val]?).getD 0
  | 54 => (([38, 39, 40, 40, 40, 40, 40] : List ℕ)[b.val]?).getD 0
  | 55 => (([41, 42, 43, 43, 43, 43, 43] : List ℕ)[b.val]?).getD 0
  | 56 => (([44, 45, 46, 46, 46, 46, 46] : List ℕ)[b.val]?).getD 0
  | 57 => (([47, 48, 49, 49, 49, 49, 49] : List ℕ)[b.val]?).getD 0
  | 58 => (([50, 51, 52, 52, 52, 52, 52] : List ℕ)[b.val]?).getD 0
  | 59 => (([53, 54, 55, 55, 55, 55, 55] : List ℕ)[b.val]?).getD 0
  | 60 => (([56, 57, 58, 58, 58, 58, 58] : List ℕ)[b.val]?).getD 0
  | 61 => (([59, 60, 61, 61, 61, 61, 61] : List ℕ)[b.val]?).getD 0
  | 62 => (([62, 63, 64, 64, 64, 64, 64] : List ℕ)[b.val]?).getD 0
  | 63 => (([65, 66, 67, 67, 67, 67, 67] : List ℕ)[b.val]?).getD 0
  | 64 => (([68, 69, 70, 70, 70, 70, 70] : List ℕ)[b.val]?).getD 0
  | 65 => (([71, 72, 73, 73, 73, 73, 73] : List ℕ)[b.val]?).getD 0
  | 66 => (([74, 75, 76, 76, 76, 76, 76] : List ℕ)[b.val]?).getD 0
  | 67 => (([77, 78, 79, 79, 79, 79, 79] : List ℕ)[b.val]?).getD 0
  | 68 => (([80, 81, 82, 82, 82, 82, 82] : List ℕ)[b.val]?).getD 0
  | 69 => (([83, 84, 85, 85, 85, 85, 85] : List ℕ)[b.val]?).getD 0
  | 70 => (([86, 87, 88, 88, 88, 88, 88] : List ℕ)[b.val]?).getD 0
  | 71 => (([89, 90, 91, 91, 91, 91, 91] : List ℕ)[b.val]?).getD 0
  | 72 => (([92, 93, 94, 94, 94, 94, 94] : List ℕ)[b.val]?).getD 0
  | 73 => (([97, 98, 99, 99, 99, 99, 99] : List ℕ)[b.val]?).getD 0
  | 74 => (([101, 102, 102, 102, 102, 102, 102] : List ℕ)[b.val]?).getD 0
  | 75 => (([103, 104, 104, 104, 104, 104, 104] : List ℕ)[b.val]?).getD 0
  | 76 => (([105, 106, 106, 106, 106, 106, 106] : List ℕ)[b.val]?).getD 0
  | 77 => (([107, 108, 108, 108, 108, 108, 108] : List ℕ)[b.val]?).getD 0
  | 78 => (([109, 110, 110, 110, 110, 110, 110] : List ℕ)[b.val]?).getD 0
  | 79 => (([111, 112, 113, 113, 113, 113, 113] : List ℕ)[b.val]?).getD 0
  | 80 => (([114, 115, 116, 116, 116, 116, 116] : List ℕ)[b.val]?).getD 0
  | 81 => (([117, 118, 119, 119, 119, 119, 119] : List ℕ)[b.val]?).getD 0
  | 82 => (([120, 121, 122, 122, 122, 122, 122] : List ℕ)[b.val]?).getD 0
  | 83 => (([123, 124, 125, 125, 125, 125, 125] : List ℕ)[b.val]?).getD 0
  | 84 => (([126, 127, 128, 128, 128, 128, 128] : List ℕ)[b.val]?).getD 0
  | 85 => (([129, 130, 131, 131, 131, 131, 131] : List ℕ)[b.val]?).getD 0
  | 86 => (([132, 133, 134, 134, 134, 134, 134] : List ℕ)[b.val]?).getD 0
  | 87 => (([135, 136, 137, 137, 137, 137, 137] : List ℕ)[b.val]?).getD 0
  | _ => 0

theorem links {k : ℕ} (hk : k < 88) (b : Fin 7) :
    queryIndex k b < 138 ∧
    (SourceAtlas82427.demand (queryIndex k b)).lower ≤ (evalData (data k).row b).T ∧
    (SourceAtlas82427.demand (queryIndex k b)).defect ≤ (evalData (data k).row b).E ∧
    (data k).potential ≤ (SourceAtlas82427.demand (queryIndex k b)).target := by
  interval_cases k <;> fin_cases b <;> decide +kernel

theorem actual_source {N k : ℕ} {S : Finset ℤ} (hk : k < 88) (b : Fin 7)
    (hN : N ≤ 2^18) (hground : S ⊆ Ground N) (hS : 2 ≤ S.card)
    (hsize : (evalData (data k).row b).T ≤ S.card)
    (hdefect : (evalData (data k).row b).E ≤ Defect S) :
    (data k).potential ≤ (Pool S).card := by
  have hl := links hk b
  have hb := SourceAtlas82427.actual_source hl.1 hN hground hS
    (hl.2.1.trans hsize) (hl.2.2.1.trans hdefect)
  exact hl.2.2.2.trans hb

#print axioms links
#print axioms actual_source
end
end JSP233.RowSources82427
