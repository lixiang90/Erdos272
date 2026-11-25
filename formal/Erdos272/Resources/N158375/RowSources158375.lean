module

public import Erdos272.Arithmetic.N158375.SourceQueryFloors158375G0
public import Erdos272.Arithmetic.N158375.SourceQueryFloors158375G1
public import Erdos272.Arithmetic.N158375.SourceQueryFloors158375G2
public import Erdos272.Arithmetic.N158375.RowGeometry158375

@[expose] public section

namespace JSP233.RowSources158375
open StarCompletion SourceBridge208 IntrinsicTriples208 CorrelatedSource158375
open SourceQueryData158375 SourceFloorSound291012 CleanupRows158375 UnitRecipeStatic208
open scoped Classical
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1000000

theorem floors {i : ℕ} (hi : i < 143) : Floor (query i).lower (query i).cutoff (query i).target := by
  by_cases h0 : i < 64
  · exact SourceQueryFloors158375G0.floors (by omega) h0
  · by_cases h1 : i < 107
    · exact SourceQueryFloors158375G1.floors (by omega) h1
    · exact SourceQueryFloors158375G2.floors (by omega) hi

def queryIndex (k b : ℕ) : ℕ := if k < 9 then 1+k*7+b else if k < 15 then 65+(k-9)*7+b else 108+(k-15)*7+b

theorem links {k : ℕ} (hk : k < 20) (b : Fin 7) :
    (query (queryIndex k b)).lower = (evalData (data k).row b).T ∧
    (query (queryIndex k b)).defect = (evalData (data k).row b).E ∧
    (query (queryIndex k b)).target = (data k).potential := by
  interval_cases k <;> fin_cases b <;> decide +kernel

theorem actual_source {N k : ℕ} {S : Finset ℤ} (hk : k < 20) (b : Fin 7)
    (hN : N ≤ 2^18) (hground : S ⊆ Ground N) (hS : 2 ≤ S.card)
    (hsize : (evalData (data k).row b).T ≤ S.card)
    (hdefect : (evalData (data k).row b).E ≤ Defect S) :
    (data k).potential ≤ (Pool S).card := by
  have hindex : queryIndex k b < 143 := by have hb := b.isLt; unfold queryIndex; split_ifs <;> omega
  have hl := links hk b
  have hs := actual_plan_source (query (queryIndex k b)) (conditions hindex) (floors hindex)
    hN hground hS (by simpa only [hl.1] using hsize) (by simpa only [hl.2.1] using hdefect)
  simpa only [hl.2.2] using hs

#print axioms floors
#print axioms links
#print axioms actual_source
end
end JSP233.RowSources158375
