module

public import Erdos272.Arithmetic.N130000.SourceQueryFloors130000G0
public import Erdos272.Arithmetic.N130000.SourceQueryFloors130000G1
public import Erdos272.Arithmetic.N130000.SourceQueryFloors130000G2
public import Erdos272.Arithmetic.N130000.SourceQueryFloors130000G3
public import Erdos272.Arithmetic.N130000.RowGeometry130000

@[expose] public section

namespace JSP233.RowSources130000
open StarCompletion SourceBridge208 IntrinsicTriples208 CorrelatedSource130000
open SourceQueryData130000 SourceFloorSound291012 CleanupRows130000 UnitRecipeStatic208
open scoped Classical
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1000000

theorem floors {i : ℕ} (hi : i < 340) : Floor (query i).lower (query i).cutoff (query i).target := by
  by_cases h0 : i < 169
  · exact SourceQueryFloors130000G0.floors (by omega) h0
  by_cases h1 : i < 254
  · exact SourceQueryFloors130000G1.floors (by omega) h1
  by_cases h2 : i < 311
  · exact SourceQueryFloors130000G2.floors (by omega) h2
  exact SourceQueryFloors130000G3.floors (by omega) hi

def queryIndex (k b : ℕ) : ℕ :=
  if k < 24 then 1+k*7+b else if k < 36 then 170+(k-24)*7+b else if k < 44 then 255+(k-36)*7+b else 312+(k-44)*7+b

theorem links {k : ℕ} (hk : k < 48) (b : Fin 7) :
    (query (queryIndex k b)).lower = (evalData (data k).row b).T ∧
    (query (queryIndex k b)).defect = (evalData (data k).row b).E ∧
    (query (queryIndex k b)).target = (data k).potential := by
  interval_cases k <;> fin_cases b <;> decide +kernel

theorem actual_source {N k : ℕ} {S : Finset ℤ} (hk : k < 48) (b : Fin 7)
    (hN : N ≤ 2^18) (hground : S ⊆ Ground N) (hS : 2 ≤ S.card)
    (hsize : (evalData (data k).row b).T ≤ S.card)
    (hdefect : (evalData (data k).row b).E ≤ Defect S) :
    (data k).potential ≤ (Pool S).card := by
  have hindex : queryIndex k b < 340 := by have hb := b.isLt; unfold queryIndex; split_ifs <;> omega
  have hl := links hk b
  have hs := actual_plan_source (query (queryIndex k b)) (conditions hindex) (floors hindex)
    hN hground hS (by simpa only [hl.1] using hsize) (by simpa only [hl.2.1] using hdefect)
  simpa only [hl.2.2] using hs

#print axioms floors
#print axioms links
#print axioms actual_source
end
end JSP233.RowSources130000
