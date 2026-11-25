module

public import Erdos272.Arithmetic.N80470.RowGeometry80470
public import Erdos272.Resources.N80470.SourceAtlas80470

@[expose] public section

namespace JSP233.RowSources80470
open StarCompletion SourceBridge208 IntrinsicTriples208 CleanupRows80470 UnitRecipeStatic208
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option maxRecDepth 200000

def queryIndex (k : ℕ) (b : Fin 7) : ℕ :=
  match k with
  | 0 => (([1, 2, 2, 2, 2, 2, 2] : List ℕ)[b.val]?).getD 0
  | 1 => (([3, 4, 5, 5, 5, 5, 5] : List ℕ)[b.val]?).getD 0
  | 2 => (([6, 7, 8, 8, 8, 8, 8] : List ℕ)[b.val]?).getD 0
  | 3 => (([9, 10, 11, 11, 11, 11, 11] : List ℕ)[b.val]?).getD 0
  | 4 => (([1, 2, 2, 2, 2, 2, 2] : List ℕ)[b.val]?).getD 0
  | 5 => (([3, 4, 5, 5, 5, 5, 5] : List ℕ)[b.val]?).getD 0
  | 6 => (([6, 7, 8, 8, 8, 8, 8] : List ℕ)[b.val]?).getD 0
  | 7 => (([12, 13, 14, 14, 14, 14, 14] : List ℕ)[b.val]?).getD 0
  | 8 => (([16, 17, 17, 17, 17, 17, 17] : List ℕ)[b.val]?).getD 0
  | 9 => (([18, 19, 19, 19, 19, 19, 19] : List ℕ)[b.val]?).getD 0
  | 10 => (([20, 21, 21, 21, 21, 21, 21] : List ℕ)[b.val]?).getD 0
  | 11 => (([22, 23, 23, 23, 23, 23, 23] : List ℕ)[b.val]?).getD 0
  | 12 => (([24, 25, 25, 25, 25, 25, 25] : List ℕ)[b.val]?).getD 0
  | 13 => (([26, 27, 28, 28, 28, 28, 28] : List ℕ)[b.val]?).getD 0
  | 14 => (([29, 30, 31, 31, 31, 31, 31] : List ℕ)[b.val]?).getD 0
  | 15 => (([32, 33, 34, 34, 34, 34, 34] : List ℕ)[b.val]?).getD 0
  | 16 => (([35, 36, 37, 37, 37, 37, 37] : List ℕ)[b.val]?).getD 0
  | 17 => (([38, 39, 40, 40, 40, 40, 40] : List ℕ)[b.val]?).getD 0
  | 18 => (([41, 42, 43, 43, 43, 43, 43] : List ℕ)[b.val]?).getD 0
  | 19 => (([44, 45, 46, 46, 46, 46, 46] : List ℕ)[b.val]?).getD 0
  | _ => 0

theorem links {k : ℕ} (hk : k < 20) (b : Fin 7) :
    queryIndex k b < 47 ∧
    (SourceAtlas80470.demand (queryIndex k b)).lower ≤ (evalData (data k).row b).T ∧
    (SourceAtlas80470.demand (queryIndex k b)).defect ≤ (evalData (data k).row b).E ∧
    (data k).potential ≤ (SourceAtlas80470.demand (queryIndex k b)).target := by
  interval_cases k <;> fin_cases b <;> decide +kernel

theorem actual_source {N k : ℕ} {S : Finset ℤ} (hk : k < 20) (b : Fin 7)
    (hN : N ≤ 2^18) (hground : S ⊆ Ground N) (hS : 2 ≤ S.card)
    (hsize : (evalData (data k).row b).T ≤ S.card)
    (hdefect : (evalData (data k).row b).E ≤ Defect S) :
    (data k).potential ≤ (Pool S).card := by
  have hl := links hk b
  have hb := SourceAtlas80470.actual_source hl.1 hN hground hS
    (hl.2.1.trans hsize) (hl.2.2.1.trans hdefect)
  exact hl.2.2.2.trans hb

#print axioms links
#print axioms actual_source
end
end JSP233.RowSources80470
