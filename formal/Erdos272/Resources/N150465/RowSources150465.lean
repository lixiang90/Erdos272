module

public import Erdos272.Arithmetic.N150465.SourceQueryFloors150465G0
public import Erdos272.Arithmetic.N150465.RowGeometry150465

@[expose] public section

namespace JSP233.RowSources150465
open StarCompletion SourceBridge208 IntrinsicTriples208 CorrelatedSource158375
open SourceQueryData150465 SourceFloorSound291012 CleanupRows150465 UnitRecipeStatic208
open scoped Classical
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1000000

theorem floors {i : ℕ} (hi : i < 85) : Floor (query i).lower (query i).cutoff (query i).target :=
  SourceQueryFloors150465G0.floors (by omega) hi

def queryIndex (k b : ℕ) : ℕ := 1+k*7+b

theorem links {k : ℕ} (hk : k < 12) (b : Fin 7) :
    (query (queryIndex k b)).lower = (evalData (data k).row b).T ∧
    (query (queryIndex k b)).defect = (evalData (data k).row b).E ∧
    (query (queryIndex k b)).target = (data k).potential := by
  interval_cases k <;> fin_cases b <;> decide +kernel

theorem actual_source {N k : ℕ} {S : Finset ℤ} (hk : k < 12) (b : Fin 7)
    (hN : N ≤ 2^18) (hground : S ⊆ Ground N) (hS : 2 ≤ S.card)
    (hsize : (evalData (data k).row b).T ≤ S.card)
    (hdefect : (evalData (data k).row b).E ≤ Defect S) :
    (data k).potential ≤ (Pool S).card := by
  have hindex : queryIndex k b < 85 := by have hb := b.isLt; unfold queryIndex; omega
  have hl := links hk b
  have hs := actual_plan_source (query (queryIndex k b)) (conditions hindex) (floors hindex)
    hN hground hS (by simpa only [hl.1] using hsize) (by simpa only [hl.2.1] using hdefect)
  simpa only [hl.2.2] using hs

#print axioms floors
#print axioms links
#print axioms actual_source
end
end JSP233.RowSources150465
