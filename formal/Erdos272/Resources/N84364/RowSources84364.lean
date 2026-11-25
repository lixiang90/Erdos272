module

public import Erdos272.Resources.N84364.SourceAtlas84364
public import Erdos272.Arithmetic.N84364.RowGeometry84364

@[expose] public section

namespace JSP233.RowSources84364
open StarCompletion SourceBridge208 IntrinsicTriples208 CleanupRows84364 UnitRecipeStatic208
set_option autoImplicit false
set_option maxHeartbeats 1000000

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
  | 10 => (([21, 22, 23, 23, 23, 23, 23] : List ℕ)[b.val]?).getD 0
  | 11 => (([24, 25, 26, 26, 26, 26, 26] : List ℕ)[b.val]?).getD 0
  | 12 => (([27, 28, 29, 29, 29, 29, 29] : List ℕ)[b.val]?).getD 0
  | 13 => (([30, 31, 32, 32, 32, 32, 32] : List ℕ)[b.val]?).getD 0
  | 14 => (([33, 34, 35, 35, 35, 35, 35] : List ℕ)[b.val]?).getD 0
  | 15 => (([36, 37, 38, 38, 38, 38, 38] : List ℕ)[b.val]?).getD 0
  | 16 => (([39, 40, 41, 41, 41, 41, 41] : List ℕ)[b.val]?).getD 0
  | 17 => (([42, 43, 44, 44, 44, 44, 44] : List ℕ)[b.val]?).getD 0
  | 18 => (([45, 46, 47, 47, 47, 47, 47] : List ℕ)[b.val]?).getD 0
  | 19 => (([48, 49, 50, 50, 50, 50, 50] : List ℕ)[b.val]?).getD 0
  | 20 => (([51, 52, 53, 53, 53, 53, 53] : List ℕ)[b.val]?).getD 0
  | 21 => (([54, 55, 56, 56, 56, 56, 56] : List ℕ)[b.val]?).getD 0
  | 22 => (([57, 58, 59, 59, 59, 59, 59] : List ℕ)[b.val]?).getD 0
  | 23 => (([60, 61, 62, 62, 62, 62, 62] : List ℕ)[b.val]?).getD 0
  | 24 => (([64, 65, 65, 65, 65, 65, 65] : List ℕ)[b.val]?).getD 0
  | 25 => (([66, 67, 67, 67, 67, 67, 67] : List ℕ)[b.val]?).getD 0
  | 26 => (([68, 69, 69, 69, 69, 69, 69] : List ℕ)[b.val]?).getD 0
  | 27 => (([70, 71, 71, 71, 71, 71, 71] : List ℕ)[b.val]?).getD 0
  | 28 => (([72, 73, 73, 73, 73, 73, 73] : List ℕ)[b.val]?).getD 0
  | 29 => (([74, 75, 75, 75, 75, 75, 75] : List ℕ)[b.val]?).getD 0
  | 30 => (([76, 77, 78, 78, 78, 78, 78] : List ℕ)[b.val]?).getD 0
  | 31 => (([79, 80, 81, 81, 81, 81, 81] : List ℕ)[b.val]?).getD 0
  | 32 => (([82, 83, 84, 84, 84, 84, 84] : List ℕ)[b.val]?).getD 0
  | 33 => (([85, 86, 87, 87, 87, 87, 87] : List ℕ)[b.val]?).getD 0
  | 34 => (([88, 89, 90, 90, 90, 90, 90] : List ℕ)[b.val]?).getD 0
  | 35 => (([91, 92, 93, 93, 93, 93, 93] : List ℕ)[b.val]?).getD 0
  | 36 => (([94, 95, 96, 96, 96, 96, 96] : List ℕ)[b.val]?).getD 0
  | 37 => (([97, 98, 99, 99, 99, 99, 99] : List ℕ)[b.val]?).getD 0
  | 38 => (([100, 101, 102, 102, 102, 102, 102] : List ℕ)[b.val]?).getD 0
  | 39 => (([103, 104, 105, 105, 105, 105, 105] : List ℕ)[b.val]?).getD 0
  | 40 => (([107, 108, 108, 108, 108, 108, 108] : List ℕ)[b.val]?).getD 0
  | 41 => (([109, 110, 111, 111, 111, 111, 111] : List ℕ)[b.val]?).getD 0
  | 42 => (([112, 113, 114, 114, 114, 114, 114] : List ℕ)[b.val]?).getD 0
  | _ => 0

theorem links {k : ℕ} (hk : k < 43) (b : Fin 7) :
    queryIndex k b < 115 ∧
    (SourceAtlas84364.demand (queryIndex k b)).lower ≤ (evalData (data k).row b).T ∧
    (SourceAtlas84364.demand (queryIndex k b)).defect ≤ (evalData (data k).row b).E ∧
    (data k).potential ≤ (SourceAtlas84364.demand (queryIndex k b)).target := by
  interval_cases k <;> fin_cases b <;> decide +kernel

theorem actual_source {N k : ℕ} {S : Finset ℤ} (hk : k < 43) (b : Fin 7)
    (hN : N ≤ 2^18) (hground : S ⊆ Ground N) (hS : 2 ≤ S.card)
    (hsize : (evalData (data k).row b).T ≤ S.card)
    (hdefect : (evalData (data k).row b).E ≤ Defect S) :
    (data k).potential ≤ (Pool S).card := by
  have hl := links hk b
  have hb := SourceAtlas84364.actual_source hl.1 hN hground hS
    (hl.2.1.trans hsize) (hl.2.2.1.trans hdefect)
  exact hl.2.2.2.trans hb

#print axioms links
#print axioms actual_source
end JSP233.RowSources84364
