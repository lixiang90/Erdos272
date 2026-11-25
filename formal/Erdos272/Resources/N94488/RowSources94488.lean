module

public import Erdos272.Resources.N94488.SourceAtlas94488
public import Erdos272.Arithmetic.N94488.RowGeometry94488

@[expose] public section

namespace JSP233.RowSources94488
open StarCompletion SourceBridge208 IntrinsicTriples208 CleanupRows94488 UnitRecipeStatic208
set_option autoImplicit false
set_option maxHeartbeats 1000000

def queryIndex (k : ℕ) (b : Fin 7) : ℕ :=
  match k with
  | 0 => (([1, 2, 2, 2, 2, 2, 2] : List ℕ)[b.val]?).getD 0
  | 1 => (([3, 4, 4, 4, 4, 4, 4] : List ℕ)[b.val]?).getD 0
  | 2 => (([5, 6, 7, 7, 7, 7, 7] : List ℕ)[b.val]?).getD 0
  | 3 => (([8, 9, 10, 10, 10, 10, 10] : List ℕ)[b.val]?).getD 0
  | 4 => (([11, 12, 13, 13, 13, 13, 13] : List ℕ)[b.val]?).getD 0
  | 5 => (([14, 15, 16, 16, 16, 16, 16] : List ℕ)[b.val]?).getD 0
  | 6 => (([17, 18, 19, 19, 19, 19, 19] : List ℕ)[b.val]?).getD 0
  | 7 => (([20, 21, 22, 22, 22, 22, 22] : List ℕ)[b.val]?).getD 0
  | 8 => (([23, 24, 25, 25, 25, 25, 25] : List ℕ)[b.val]?).getD 0
  | 9 => (([26, 27, 28, 28, 28, 28, 28] : List ℕ)[b.val]?).getD 0
  | 10 => (([29, 30, 31, 31, 31, 31, 31] : List ℕ)[b.val]?).getD 0
  | 11 => (([32, 33, 34, 34, 34, 34, 34] : List ℕ)[b.val]?).getD 0
  | 12 => (([35, 36, 37, 37, 37, 37, 37] : List ℕ)[b.val]?).getD 0
  | 13 => (([38, 39, 40, 40, 40, 40, 40] : List ℕ)[b.val]?).getD 0
  | 14 => (([41, 42, 43, 43, 43, 43, 43] : List ℕ)[b.val]?).getD 0
  | 15 => (([44, 45, 46, 46, 46, 46, 46] : List ℕ)[b.val]?).getD 0
  | 16 => (([47, 48, 49, 49, 49, 49, 49] : List ℕ)[b.val]?).getD 0
  | 17 => (([50, 51, 52, 52, 52, 52, 52] : List ℕ)[b.val]?).getD 0
  | 18 => (([53, 54, 55, 55, 55, 55, 55] : List ℕ)[b.val]?).getD 0
  | 19 => (([56, 57, 58, 58, 58, 58, 58] : List ℕ)[b.val]?).getD 0
  | 20 => (([59, 60, 61, 61, 61, 61, 61] : List ℕ)[b.val]?).getD 0
  | 21 => (([62, 63, 64, 64, 64, 64, 64] : List ℕ)[b.val]?).getD 0
  | 22 => (([65, 66, 67, 68, 68, 68, 68] : List ℕ)[b.val]?).getD 0
  | 23 => (([69, 70, 71, 72, 72, 72, 72] : List ℕ)[b.val]?).getD 0
  | 24 => (([73, 74, 75, 76, 76, 76, 76] : List ℕ)[b.val]?).getD 0
  | 25 => (([77, 78, 79, 80, 80, 80, 80] : List ℕ)[b.val]?).getD 0
  | 26 => (([81, 82, 83, 84, 84, 84, 84] : List ℕ)[b.val]?).getD 0
  | 27 => (([85, 86, 87, 88, 88, 88, 88] : List ℕ)[b.val]?).getD 0
  | 28 => (([90, 91, 91, 91, 91, 91, 91] : List ℕ)[b.val]?).getD 0
  | 29 => (([92, 93, 94, 94, 94, 94, 94] : List ℕ)[b.val]?).getD 0
  | 30 => (([95, 96, 97, 97, 97, 97, 97] : List ℕ)[b.val]?).getD 0
  | 31 => (([98, 99, 100, 100, 100, 100, 100] : List ℕ)[b.val]?).getD 0
  | 32 => (([101, 102, 103, 103, 103, 103, 103] : List ℕ)[b.val]?).getD 0
  | 33 => (([104, 105, 106, 106, 106, 106, 106] : List ℕ)[b.val]?).getD 0
  | 34 => (([107, 108, 109, 109, 109, 109, 109] : List ℕ)[b.val]?).getD 0
  | 35 => (([110, 111, 112, 112, 112, 112, 112] : List ℕ)[b.val]?).getD 0
  | 36 => (([113, 114, 115, 115, 115, 115, 115] : List ℕ)[b.val]?).getD 0
  | 37 => (([116, 117, 118, 118, 118, 118, 118] : List ℕ)[b.val]?).getD 0
  | 38 => (([119, 120, 121, 121, 121, 121, 121] : List ℕ)[b.val]?).getD 0
  | 39 => (([122, 123, 124, 125, 125, 125, 125] : List ℕ)[b.val]?).getD 0
  | 40 => (([126, 127, 128, 129, 129, 129, 129] : List ℕ)[b.val]?).getD 0
  | 41 => (([130, 131, 132, 133, 133, 133, 133] : List ℕ)[b.val]?).getD 0
  | 42 => (([135, 136, 136, 136, 136, 136, 136] : List ℕ)[b.val]?).getD 0
  | 43 => (([137, 138, 139, 139, 139, 139, 139] : List ℕ)[b.val]?).getD 0
  | 44 => (([140, 141, 142, 142, 142, 142, 142] : List ℕ)[b.val]?).getD 0
  | 45 => (([143, 144, 145, 145, 145, 145, 145] : List ℕ)[b.val]?).getD 0
  | 46 => (([146, 147, 148, 148, 148, 148, 148] : List ℕ)[b.val]?).getD 0
  | 47 => (([149, 150, 151, 151, 151, 151, 151] : List ℕ)[b.val]?).getD 0
  | 48 => (([152, 153, 154, 154, 154, 154, 154] : List ℕ)[b.val]?).getD 0
  | 49 => (([155, 156, 157, 157, 157, 157, 157] : List ℕ)[b.val]?).getD 0
  | 50 => (([158, 159, 160, 161, 161, 161, 161] : List ℕ)[b.val]?).getD 0
  | 51 => (([162, 163, 164, 165, 165, 165, 165] : List ℕ)[b.val]?).getD 0
  | 52 => (([167, 168, 168, 168, 168, 168, 168] : List ℕ)[b.val]?).getD 0
  | 53 => (([169, 170, 171, 171, 171, 171, 171] : List ℕ)[b.val]?).getD 0
  | 54 => (([172, 173, 174, 174, 174, 174, 174] : List ℕ)[b.val]?).getD 0
  | 55 => (([175, 176, 177, 177, 177, 177, 177] : List ℕ)[b.val]?).getD 0
  | 56 => (([178, 179, 180, 180, 180, 180, 180] : List ℕ)[b.val]?).getD 0
  | 57 => (([181, 182, 183, 183, 183, 183, 183] : List ℕ)[b.val]?).getD 0
  | 58 => (([184, 185, 186, 186, 186, 186, 186] : List ℕ)[b.val]?).getD 0
  | 59 => (([187, 188, 189, 189, 189, 189, 189] : List ℕ)[b.val]?).getD 0
  | 60 => (([190, 191, 192, 193, 193, 193, 193] : List ℕ)[b.val]?).getD 0
  | 61 => (([194, 195, 196, 197, 197, 197, 197] : List ℕ)[b.val]?).getD 0
  | 62 => (([199, 200, 201, 201, 201, 201, 201] : List ℕ)[b.val]?).getD 0
  | 63 => (([202, 203, 204, 204, 204, 204, 204] : List ℕ)[b.val]?).getD 0
  | 64 => (([205, 206, 207, 207, 207, 207, 207] : List ℕ)[b.val]?).getD 0
  | 65 => (([208, 209, 210, 210, 210, 210, 210] : List ℕ)[b.val]?).getD 0
  | 66 => (([211, 212, 213, 214, 214, 214, 214] : List ℕ)[b.val]?).getD 0
  | 67 => (([215, 216, 217, 218, 218, 218, 218] : List ℕ)[b.val]?).getD 0
  | 68 => (([220, 221, 221, 221, 221, 221, 221] : List ℕ)[b.val]?).getD 0
  | 69 => (([222, 223, 224, 224, 224, 224, 224] : List ℕ)[b.val]?).getD 0
  | 70 => (([225, 226, 227, 227, 227, 227, 227] : List ℕ)[b.val]?).getD 0
  | _ => 0

theorem links {k : ℕ} (hk : k < 71) (b : Fin 7) :
    queryIndex k b < 228 ∧
    (SourceAtlas94488.demand (queryIndex k b)).lower ≤ (evalData (data k).row b).T ∧
    (SourceAtlas94488.demand (queryIndex k b)).defect ≤ (evalData (data k).row b).E ∧
    (data k).potential ≤ (SourceAtlas94488.demand (queryIndex k b)).target := by
  interval_cases k <;> fin_cases b <;> decide +kernel

theorem actual_source {N k : ℕ} {S : Finset ℤ} (hk : k < 71) (b : Fin 7)
    (hN : N ≤ 2^18) (hground : S ⊆ Ground N) (hS : 2 ≤ S.card)
    (hsize : (evalData (data k).row b).T ≤ S.card)
    (hdefect : (evalData (data k).row b).E ≤ Defect S) :
    (data k).potential ≤ (Pool S).card := by
  have hl := links hk b
  have hb := SourceAtlas94488.actual_source hl.1 hN hground hS
    (hl.2.1.trans hsize) (hl.2.2.1.trans hdefect)
  exact hl.2.2.2.trans hb

#print axioms links
#print axioms actual_source
end JSP233.RowSources94488
