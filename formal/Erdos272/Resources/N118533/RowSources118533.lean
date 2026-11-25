module

public import Erdos272.Resources.N118533.SourceAtlas118533
public import Erdos272.Arithmetic.N118533.RowGeometry118533

@[expose] public section

namespace JSP233.RowSources118533
open StarCompletion SourceBridge208 IntrinsicTriples208 CleanupRows118533 UnitRecipeStatic208
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
  | 8 => (([24, 25, 26, 27, 27, 27, 27] : List ℕ)[b.val]?).getD 0
  | 9 => (([28, 29, 30, 31, 31, 31, 31] : List ℕ)[b.val]?).getD 0
  | 10 => (([32, 33, 34, 35, 35, 35, 35] : List ℕ)[b.val]?).getD 0
  | 11 => (([36, 37, 38, 39, 39, 39, 39] : List ℕ)[b.val]?).getD 0
  | 12 => (([41, 42, 43, 43, 43, 43, 43] : List ℕ)[b.val]?).getD 0
  | 13 => (([44, 45, 46, 46, 46, 46, 46] : List ℕ)[b.val]?).getD 0
  | 14 => (([47, 48, 49, 49, 49, 49, 49] : List ℕ)[b.val]?).getD 0
  | 15 => (([50, 51, 52, 52, 52, 52, 52] : List ℕ)[b.val]?).getD 0
  | 16 => (([53, 54, 55, 56, 56, 56, 56] : List ℕ)[b.val]?).getD 0
  | 17 => (([57, 58, 59, 60, 60, 60, 60] : List ℕ)[b.val]?).getD 0
  | 18 => (([62, 63, 64, 64, 64, 64, 64] : List ℕ)[b.val]?).getD 0
  | 19 => (([65, 66, 67, 67, 67, 67, 67] : List ℕ)[b.val]?).getD 0
  | 20 => (([68, 69, 70, 70, 70, 70, 70] : List ℕ)[b.val]?).getD 0
  | _ => 0

theorem links {k : ℕ} (hk : k < 21) (b : Fin 7) :
    queryIndex k b < 71 ∧
    (SourceAtlas118533.demand (queryIndex k b)).lower ≤ (evalData (data k).row b).T ∧
    (SourceAtlas118533.demand (queryIndex k b)).defect ≤ (evalData (data k).row b).E ∧
    (data k).potential ≤ (SourceAtlas118533.demand (queryIndex k b)).target := by
  interval_cases k <;> fin_cases b <;> decide +kernel

theorem actual_source {N k : ℕ} {S : Finset ℤ} (hk : k < 21) (b : Fin 7)
    (hN : N ≤ 2^18) (hground : S ⊆ Ground N) (hS : 2 ≤ S.card)
    (hsize : (evalData (data k).row b).T ≤ S.card)
    (hdefect : (evalData (data k).row b).E ≤ Defect S) :
    (data k).potential ≤ (Pool S).card := by
  have hl := links hk b
  have hb := SourceAtlas118533.actual_source hl.1 hN hground hS
    (hl.2.1.trans hsize) (hl.2.2.1.trans hdefect)
  exact hl.2.2.2.trans hb

#print axioms links
#print axioms actual_source
end JSP233.RowSources118533
