module

public import Erdos272.Resources.N86412.SourceAtlas86412
public import Erdos272.Arithmetic.N86412.RowGeometry86412

@[expose] public section

namespace JSP233.RowSources86412
open StarCompletion SourceBridge208 IntrinsicTriples208 CleanupRows86412 UnitRecipeStatic208
set_option autoImplicit false
set_option maxHeartbeats 1000000

def queryIndex (k : ℕ) (b : Fin 7) : ℕ :=
  match k with
  | 0 => (([1, 2, 2, 2, 2, 2, 2] : List ℕ)[b.val]?).getD 0
  | 1 => (([3, 4, 4, 4, 4, 4, 4] : List ℕ)[b.val]?).getD 0
  | 2 => (([5, 6, 6, 6, 6, 6, 6] : List ℕ)[b.val]?).getD 0
  | 3 => (([7, 8, 9, 9, 9, 9, 9] : List ℕ)[b.val]?).getD 0
  | 4 => (([10, 11, 12, 12, 12, 12, 12] : List ℕ)[b.val]?).getD 0
  | 5 => (([13, 14, 15, 15, 15, 15, 15] : List ℕ)[b.val]?).getD 0
  | 6 => (([16, 17, 18, 18, 18, 18, 18] : List ℕ)[b.val]?).getD 0
  | 7 => (([19, 20, 21, 21, 21, 21, 21] : List ℕ)[b.val]?).getD 0
  | 8 => (([22, 23, 24, 24, 24, 24, 24] : List ℕ)[b.val]?).getD 0
  | 9 => (([25, 26, 27, 27, 27, 27, 27] : List ℕ)[b.val]?).getD 0
  | 10 => (([28, 29, 30, 30, 30, 30, 30] : List ℕ)[b.val]?).getD 0
  | 11 => (([31, 32, 33, 33, 33, 33, 33] : List ℕ)[b.val]?).getD 0
  | 12 => (([34, 35, 36, 36, 36, 36, 36] : List ℕ)[b.val]?).getD 0
  | 13 => (([37, 38, 39, 39, 39, 39, 39] : List ℕ)[b.val]?).getD 0
  | 14 => (([40, 41, 42, 42, 42, 42, 42] : List ℕ)[b.val]?).getD 0
  | 15 => (([43, 44, 45, 45, 45, 45, 45] : List ℕ)[b.val]?).getD 0
  | 16 => (([46, 47, 48, 48, 48, 48, 48] : List ℕ)[b.val]?).getD 0
  | 17 => (([49, 50, 51, 51, 51, 51, 51] : List ℕ)[b.val]?).getD 0
  | 18 => (([52, 53, 54, 54, 54, 54, 54] : List ℕ)[b.val]?).getD 0
  | 19 => (([55, 56, 57, 57, 57, 57, 57] : List ℕ)[b.val]?).getD 0
  | 20 => (([58, 59, 60, 60, 60, 60, 60] : List ℕ)[b.val]?).getD 0
  | 21 => (([61, 62, 63, 63, 63, 63, 63] : List ℕ)[b.val]?).getD 0
  | 22 => (([64, 65, 66, 66, 66, 66, 66] : List ℕ)[b.val]?).getD 0
  | 23 => (([67, 68, 69, 69, 69, 69, 69] : List ℕ)[b.val]?).getD 0
  | 24 => (([70, 71, 72, 72, 72, 72, 72] : List ℕ)[b.val]?).getD 0
  | 25 => (([73, 74, 75, 75, 75, 75, 75] : List ℕ)[b.val]?).getD 0
  | 26 => (([76, 77, 78, 78, 78, 78, 78] : List ℕ)[b.val]?).getD 0
  | 27 => (([79, 80, 81, 81, 81, 81, 81] : List ℕ)[b.val]?).getD 0
  | 28 => (([82, 83, 84, 84, 84, 84, 84] : List ℕ)[b.val]?).getD 0
  | 29 => (([85, 86, 87, 87, 87, 87, 87] : List ℕ)[b.val]?).getD 0
  | 30 => (([88, 89, 90, 90, 90, 90, 90] : List ℕ)[b.val]?).getD 0
  | 31 => (([91, 92, 93, 93, 93, 93, 93] : List ℕ)[b.val]?).getD 0
  | 32 => (([94, 95, 96, 96, 96, 96, 96] : List ℕ)[b.val]?).getD 0
  | 33 => (([97, 98, 99, 99, 99, 99, 99] : List ℕ)[b.val]?).getD 0
  | 34 => (([100, 101, 102, 102, 102, 102, 102] : List ℕ)[b.val]?).getD 0
  | 35 => (([103, 104, 105, 106, 106, 106, 106] : List ℕ)[b.val]?).getD 0
  | 36 => (([108, 109, 109, 109, 109, 109, 109] : List ℕ)[b.val]?).getD 0
  | 37 => (([110, 111, 112, 112, 112, 112, 112] : List ℕ)[b.val]?).getD 0
  | 38 => (([113, 114, 115, 115, 115, 115, 115] : List ℕ)[b.val]?).getD 0
  | 39 => (([116, 117, 118, 118, 118, 118, 118] : List ℕ)[b.val]?).getD 0
  | 40 => (([119, 120, 121, 121, 121, 121, 121] : List ℕ)[b.val]?).getD 0
  | 41 => (([122, 123, 124, 124, 124, 124, 124] : List ℕ)[b.val]?).getD 0
  | 42 => (([125, 126, 127, 127, 127, 127, 127] : List ℕ)[b.val]?).getD 0
  | 43 => (([128, 129, 130, 130, 130, 130, 130] : List ℕ)[b.val]?).getD 0
  | 44 => (([131, 132, 133, 133, 133, 133, 133] : List ℕ)[b.val]?).getD 0
  | 45 => (([134, 135, 136, 136, 136, 136, 136] : List ℕ)[b.val]?).getD 0
  | 46 => (([137, 138, 139, 139, 139, 139, 139] : List ℕ)[b.val]?).getD 0
  | 47 => (([140, 141, 142, 142, 142, 142, 142] : List ℕ)[b.val]?).getD 0
  | 48 => (([144, 145, 145, 145, 145, 145, 145] : List ℕ)[b.val]?).getD 0
  | 49 => (([146, 147, 148, 148, 148, 148, 148] : List ℕ)[b.val]?).getD 0
  | 50 => (([149, 150, 151, 151, 151, 151, 151] : List ℕ)[b.val]?).getD 0
  | _ => 0

theorem links {k : ℕ} (hk : k < 51) (b : Fin 7) :
    queryIndex k b < 152 ∧
    (SourceAtlas86412.demand (queryIndex k b)).lower ≤ (evalData (data k).row b).T ∧
    (SourceAtlas86412.demand (queryIndex k b)).defect ≤ (evalData (data k).row b).E ∧
    (data k).potential ≤ (SourceAtlas86412.demand (queryIndex k b)).target := by
  interval_cases k <;> fin_cases b <;> decide +kernel

theorem actual_source {N k : ℕ} {S : Finset ℤ} (hk : k < 51) (b : Fin 7)
    (hN : N ≤ 2^18) (hground : S ⊆ Ground N) (hS : 2 ≤ S.card)
    (hsize : (evalData (data k).row b).T ≤ S.card)
    (hdefect : (evalData (data k).row b).E ≤ Defect S) :
    (data k).potential ≤ (Pool S).card := by
  have hl := links hk b
  have hb := SourceAtlas86412.actual_source hl.1 hN hground hS
    (hl.2.1.trans hsize) (hl.2.2.1.trans hdefect)
  exact hl.2.2.2.trans hb

#print axioms links
#print axioms actual_source
end JSP233.RowSources86412
