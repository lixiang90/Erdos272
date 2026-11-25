module

public import Erdos272.Resources.N109474.SourceAtlas109474
public import Erdos272.Arithmetic.N109474.RowGeometry109474

@[expose] public section

namespace JSP233.RowSources109474
open StarCompletion SourceBridge208 IntrinsicTriples208 CleanupRows109474 UnitRecipeStatic208
set_option autoImplicit false
set_option maxHeartbeats 1000000

def queryIndex (k : ℕ) (b : Fin 7) : ℕ :=
  match k with
  | 0 => (([1, 2, 2, 2, 2, 2, 2] : List ℕ)[b.val]?).getD 0
  | 1 => (([3, 4, 5, 5, 5, 5, 5] : List ℕ)[b.val]?).getD 0
  | 2 => (([6, 7, 8, 8, 8, 8, 8] : List ℕ)[b.val]?).getD 0
  | 3 => (([9, 10, 11, 11, 11, 11, 11] : List ℕ)[b.val]?).getD 0
  | 4 => (([12, 13, 14, 14, 14, 14, 14] : List ℕ)[b.val]?).getD 0
  | 5 => (([15, 16, 17, 17, 17, 17, 17] : List ℕ)[b.val]?).getD 0
  | 6 => (([18, 19, 20, 20, 20, 20, 20] : List ℕ)[b.val]?).getD 0
  | 7 => (([21, 22, 23, 23, 23, 23, 23] : List ℕ)[b.val]?).getD 0
  | 8 => (([24, 25, 26, 26, 26, 26, 26] : List ℕ)[b.val]?).getD 0
  | 9 => (([27, 28, 29, 29, 29, 29, 29] : List ℕ)[b.val]?).getD 0
  | 10 => (([30, 31, 32, 32, 32, 32, 32] : List ℕ)[b.val]?).getD 0
  | 11 => (([33, 34, 35, 35, 35, 35, 35] : List ℕ)[b.val]?).getD 0
  | 12 => (([36, 37, 38, 38, 38, 38, 38] : List ℕ)[b.val]?).getD 0
  | 13 => (([39, 40, 41, 41, 41, 41, 41] : List ℕ)[b.val]?).getD 0
  | 14 => (([42, 43, 44, 44, 44, 44, 44] : List ℕ)[b.val]?).getD 0
  | 15 => (([45, 46, 47, 47, 47, 47, 47] : List ℕ)[b.val]?).getD 0
  | 16 => (([48, 49, 50, 51, 51, 51, 51] : List ℕ)[b.val]?).getD 0
  | 17 => (([52, 53, 54, 55, 55, 55, 55] : List ℕ)[b.val]?).getD 0
  | 18 => (([56, 57, 58, 59, 59, 59, 59] : List ℕ)[b.val]?).getD 0
  | 19 => (([60, 61, 62, 63, 63, 63, 63] : List ℕ)[b.val]?).getD 0
  | 20 => (([64, 65, 66, 67, 67, 67, 67] : List ℕ)[b.val]?).getD 0
  | 21 => (([68, 69, 70, 71, 71, 71, 71] : List ℕ)[b.val]?).getD 0
  | 22 => (([72, 73, 74, 75, 75, 75, 75] : List ℕ)[b.val]?).getD 0
  | 23 => (([76, 77, 78, 79, 79, 79, 79] : List ℕ)[b.val]?).getD 0
  | 24 => (([81, 82, 82, 82, 82, 82, 82] : List ℕ)[b.val]?).getD 0
  | 25 => (([83, 84, 85, 85, 85, 85, 85] : List ℕ)[b.val]?).getD 0
  | 26 => (([86, 87, 88, 88, 88, 88, 88] : List ℕ)[b.val]?).getD 0
  | 27 => (([89, 90, 91, 91, 91, 91, 91] : List ℕ)[b.val]?).getD 0
  | 28 => (([92, 93, 94, 94, 94, 94, 94] : List ℕ)[b.val]?).getD 0
  | 29 => (([95, 96, 97, 97, 97, 97, 97] : List ℕ)[b.val]?).getD 0
  | 30 => (([98, 99, 100, 100, 100, 100, 100] : List ℕ)[b.val]?).getD 0
  | 31 => (([101, 102, 103, 103, 103, 103, 103] : List ℕ)[b.val]?).getD 0
  | 32 => (([104, 105, 106, 106, 106, 106, 106] : List ℕ)[b.val]?).getD 0
  | 33 => (([107, 108, 109, 109, 109, 109, 109] : List ℕ)[b.val]?).getD 0
  | 34 => (([110, 111, 112, 113, 113, 113, 113] : List ℕ)[b.val]?).getD 0
  | 35 => (([114, 115, 116, 117, 117, 117, 117] : List ℕ)[b.val]?).getD 0
  | 36 => (([118, 119, 120, 121, 121, 121, 121] : List ℕ)[b.val]?).getD 0
  | 37 => (([122, 123, 124, 125, 125, 125, 125] : List ℕ)[b.val]?).getD 0
  | 38 => (([126, 127, 128, 129, 129, 129, 129] : List ℕ)[b.val]?).getD 0
  | 39 => (([130, 131, 132, 133, 133, 133, 133] : List ℕ)[b.val]?).getD 0
  | 40 => (([135, 136, 136, 136, 136, 136, 136] : List ℕ)[b.val]?).getD 0
  | 41 => (([137, 138, 139, 139, 139, 139, 139] : List ℕ)[b.val]?).getD 0
  | 42 => (([140, 141, 142, 142, 142, 142, 142] : List ℕ)[b.val]?).getD 0
  | 43 => (([143, 144, 145, 145, 145, 145, 145] : List ℕ)[b.val]?).getD 0
  | 44 => (([146, 147, 148, 148, 148, 148, 148] : List ℕ)[b.val]?).getD 0
  | 45 => (([149, 150, 151, 151, 151, 151, 151] : List ℕ)[b.val]?).getD 0
  | 46 => (([152, 153, 154, 154, 154, 154, 154] : List ℕ)[b.val]?).getD 0
  | 47 => (([155, 156, 157, 157, 157, 157, 157] : List ℕ)[b.val]?).getD 0
  | 48 => (([158, 159, 160, 160, 160, 160, 160] : List ℕ)[b.val]?).getD 0
  | 49 => (([161, 162, 163, 163, 163, 163, 163] : List ℕ)[b.val]?).getD 0
  | 50 => (([164, 165, 166, 167, 167, 167, 167] : List ℕ)[b.val]?).getD 0
  | 51 => (([168, 169, 170, 171, 171, 171, 171] : List ℕ)[b.val]?).getD 0
  | 52 => (([172, 173, 174, 175, 175, 175, 175] : List ℕ)[b.val]?).getD 0
  | 53 => (([176, 177, 178, 179, 179, 179, 179] : List ℕ)[b.val]?).getD 0
  | 54 => (([180, 181, 182, 183, 183, 183, 183] : List ℕ)[b.val]?).getD 0
  | 55 => (([184, 185, 186, 187, 187, 187, 187] : List ℕ)[b.val]?).getD 0
  | 56 => (([189, 190, 191, 191, 191, 191, 191] : List ℕ)[b.val]?).getD 0
  | 57 => (([192, 193, 194, 194, 194, 194, 194] : List ℕ)[b.val]?).getD 0
  | 58 => (([195, 196, 197, 197, 197, 197, 197] : List ℕ)[b.val]?).getD 0
  | _ => 0

theorem links {k : ℕ} (hk : k < 59) (b : Fin 7) :
    queryIndex k b < 198 ∧
    (SourceAtlas109474.demand (queryIndex k b)).lower ≤ (evalData (data k).row b).T ∧
    (SourceAtlas109474.demand (queryIndex k b)).defect ≤ (evalData (data k).row b).E ∧
    (data k).potential ≤ (SourceAtlas109474.demand (queryIndex k b)).target := by
  interval_cases k <;> fin_cases b <;> decide +kernel

theorem actual_source {N k : ℕ} {S : Finset ℤ} (hk : k < 59) (b : Fin 7)
    (hN : N ≤ 2^18) (hground : S ⊆ Ground N) (hS : 2 ≤ S.card)
    (hsize : (evalData (data k).row b).T ≤ S.card)
    (hdefect : (evalData (data k).row b).E ≤ Defect S) :
    (data k).potential ≤ (Pool S).card := by
  have hl := links hk b
  have hb := SourceAtlas109474.actual_source hl.1 hN hground hS
    (hl.2.1.trans hsize) (hl.2.2.1.trans hdefect)
  exact hl.2.2.2.trans hb

#print axioms links
#print axioms actual_source
end JSP233.RowSources109474
