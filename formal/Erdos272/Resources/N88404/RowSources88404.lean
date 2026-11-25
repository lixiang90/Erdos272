module

public import Erdos272.Resources.N88404.SourceAtlas88404
public import Erdos272.Arithmetic.N88404.RowGeometry88404

@[expose] public section

namespace JSP233.RowSources88404
open StarCompletion SourceBridge208 IntrinsicTriples208 CleanupRows88404 UnitRecipeStatic208
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
  | 35 => (([103, 104, 105, 105, 105, 105, 105] : List ℕ)[b.val]?).getD 0
  | 36 => (([106, 107, 108, 108, 108, 108, 108] : List ℕ)[b.val]?).getD 0
  | 37 => (([109, 110, 111, 111, 111, 111, 111] : List ℕ)[b.val]?).getD 0
  | 38 => (([112, 113, 114, 114, 114, 114, 114] : List ℕ)[b.val]?).getD 0
  | 39 => (([115, 116, 117, 117, 117, 117, 117] : List ℕ)[b.val]?).getD 0
  | 40 => (([118, 119, 120, 120, 120, 120, 120] : List ℕ)[b.val]?).getD 0
  | 41 => (([121, 122, 123, 123, 123, 123, 123] : List ℕ)[b.val]?).getD 0
  | 42 => (([124, 125, 126, 126, 126, 126, 126] : List ℕ)[b.val]?).getD 0
  | 43 => (([127, 128, 129, 129, 129, 129, 129] : List ℕ)[b.val]?).getD 0
  | 44 => (([130, 131, 132, 132, 132, 132, 132] : List ℕ)[b.val]?).getD 0
  | 45 => (([133, 134, 135, 135, 135, 135, 135] : List ℕ)[b.val]?).getD 0
  | 46 => (([136, 137, 138, 138, 138, 138, 138] : List ℕ)[b.val]?).getD 0
  | 47 => (([139, 140, 141, 141, 141, 141, 141] : List ℕ)[b.val]?).getD 0
  | 48 => (([142, 143, 144, 145, 145, 145, 145] : List ℕ)[b.val]?).getD 0
  | 49 => (([146, 147, 148, 149, 149, 149, 149] : List ℕ)[b.val]?).getD 0
  | 50 => (([150, 151, 152, 153, 153, 153, 153] : List ℕ)[b.val]?).getD 0
  | 51 => (([154, 155, 156, 157, 157, 157, 157] : List ℕ)[b.val]?).getD 0
  | 52 => (([159, 160, 160, 160, 160, 160, 160] : List ℕ)[b.val]?).getD 0
  | 53 => (([161, 162, 163, 163, 163, 163, 163] : List ℕ)[b.val]?).getD 0
  | 54 => (([164, 165, 166, 166, 166, 166, 166] : List ℕ)[b.val]?).getD 0
  | 55 => (([167, 168, 169, 169, 169, 169, 169] : List ℕ)[b.val]?).getD 0
  | 56 => (([170, 171, 172, 172, 172, 172, 172] : List ℕ)[b.val]?).getD 0
  | 57 => (([173, 174, 175, 175, 175, 175, 175] : List ℕ)[b.val]?).getD 0
  | 58 => (([176, 177, 178, 178, 178, 178, 178] : List ℕ)[b.val]?).getD 0
  | 59 => (([179, 180, 181, 181, 181, 181, 181] : List ℕ)[b.val]?).getD 0
  | 60 => (([182, 183, 184, 184, 184, 184, 184] : List ℕ)[b.val]?).getD 0
  | 61 => (([185, 186, 187, 187, 187, 187, 187] : List ℕ)[b.val]?).getD 0
  | 62 => (([188, 189, 190, 190, 190, 190, 190] : List ℕ)[b.val]?).getD 0
  | 63 => (([191, 192, 193, 193, 193, 193, 193] : List ℕ)[b.val]?).getD 0
  | 64 => (([194, 195, 196, 196, 196, 196, 196] : List ℕ)[b.val]?).getD 0
  | 65 => (([197, 198, 199, 200, 200, 200, 200] : List ℕ)[b.val]?).getD 0
  | 66 => (([201, 202, 203, 204, 204, 204, 204] : List ℕ)[b.val]?).getD 0
  | 67 => (([205, 206, 207, 208, 208, 208, 208] : List ℕ)[b.val]?).getD 0
  | 68 => (([210, 211, 211, 211, 211, 211, 211] : List ℕ)[b.val]?).getD 0
  | 69 => (([212, 213, 214, 214, 214, 214, 214] : List ℕ)[b.val]?).getD 0
  | 70 => (([215, 216, 217, 217, 217, 217, 217] : List ℕ)[b.val]?).getD 0
  | 71 => (([218, 219, 220, 220, 220, 220, 220] : List ℕ)[b.val]?).getD 0
  | 72 => (([221, 222, 223, 223, 223, 223, 223] : List ℕ)[b.val]?).getD 0
  | 73 => (([224, 225, 226, 226, 226, 226, 226] : List ℕ)[b.val]?).getD 0
  | 74 => (([227, 228, 229, 229, 229, 229, 229] : List ℕ)[b.val]?).getD 0
  | 75 => (([230, 231, 232, 232, 232, 232, 232] : List ℕ)[b.val]?).getD 0
  | 76 => (([233, 234, 235, 235, 235, 235, 235] : List ℕ)[b.val]?).getD 0
  | 77 => (([236, 237, 238, 239, 239, 239, 239] : List ℕ)[b.val]?).getD 0
  | 78 => (([241, 242, 242, 242, 242, 242, 242] : List ℕ)[b.val]?).getD 0
  | 79 => (([243, 244, 245, 245, 245, 245, 245] : List ℕ)[b.val]?).getD 0
  | 80 => (([246, 247, 248, 248, 248, 248, 248] : List ℕ)[b.val]?).getD 0
  | _ => 0

theorem links {k : ℕ} (hk : k < 81) (b : Fin 7) :
    queryIndex k b < 249 ∧
    (SourceAtlas88404.demand (queryIndex k b)).lower ≤ (evalData (data k).row b).T ∧
    (SourceAtlas88404.demand (queryIndex k b)).defect ≤ (evalData (data k).row b).E ∧
    (data k).potential ≤ (SourceAtlas88404.demand (queryIndex k b)).target := by
  interval_cases k <;> fin_cases b <;> decide +kernel

theorem actual_source {N k : ℕ} {S : Finset ℤ} (hk : k < 81) (b : Fin 7)
    (hN : N ≤ 2^18) (hground : S ⊆ Ground N) (hS : 2 ≤ S.card)
    (hsize : (evalData (data k).row b).T ≤ S.card)
    (hdefect : (evalData (data k).row b).E ≤ Defect S) :
    (data k).potential ≤ (Pool S).card := by
  have hl := links hk b
  have hb := SourceAtlas88404.actual_source hl.1 hN hground hS
    (hl.2.1.trans hsize) (hl.2.2.1.trans hdefect)
  exact hl.2.2.2.trans hb

#print axioms links
#print axioms actual_source
end JSP233.RowSources88404
