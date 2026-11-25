module

public import Erdos272.Counting.N65968.FullSurplusFamily65968
public import Erdos272.Resources.ActualUnitLayer208
public import Erdos272.Arithmetic.N291012.RowStatic291012

@[expose] public section

namespace JSP233.FullSurplusLayer65968
open StarCompletion APGeometry NearAP36 SourceBridge208 IntrinsicTriples208 SevenFamily208
open CrossBandCredit208 CrossBandCleanup208 CleanupMachineSound208
open ActualUnitRecipe208 UnitRecipeStatic208 RowStatic291012
open scoped Classical BigOperators
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1000000

def Upper (v : CleanupRows291012.Data) (N L : ℕ) : ℝ :=
  (N : ℝ)^2*v.residualUnits/1000000000000+(253/35 : ℝ)*N+
    (L : ℝ)+(N : ℝ)*((v.total.net : ℝ)/1000000000000)

theorem actual_near_bound {N ell W L : ℕ} {psi : ℕ → ℝ}
    {A F : Finset (Finset ℤ)} {A₀ : Finset ℤ}
    (v : CleanupRows291012.Data) (hp : Static v)
    (p : ActualUnitCut291012.CutRecipe N v.memberFloor v.row.i ell 12 psi A)
    (hdata : ∀ b : CrossBandCredit208.Band, p.data b=evalData v.row b)
    (hf : CleanupEval208.ChunkFacts (toRow v.row) 1 v.steps (toTotals v.total))
    (hlo : v.row.low ≤ N) (hhi : N ≤ v.row.high)
    (hlegalA : Legal (Ground N) A) (hbad : ∀ S ∈ A, ¬IsAP S)
    (hsize : ∀ S ∈ A, v.memberFloor ≤ S.card) (hsparse : ∀ S ∈ A, 12*S.card ≤ N)
    (hlegalF : Legal (Ground N) F) (hAF : A ⊆ F)
    (hA₀ : A₀ ∈ F) (hW : A₀.card ≤ W)
    (hlight : FullSurplusFamily65968.RowLight (toRow v.row)
      (by simpa only [toRow,List.length_map] using hp.length) v.steps W ≤ L)
    (hresidual : ResidualAggregate208.Price v.row.i (ResidualTwoCensus208.H v.memberFloor) ≤
      (v.residualUnits : ℝ)/1000000000000) :
    ((PoolNear A psi ell).card : ℝ) ≤ Upper v N L := by
  obtain ⟨s,hsN,hsD,hsM,hse,hsF,hmap,hvalid⟩ :=
    ActualUnitCut291012.actual_system p hp.member_two hp.defect_two hp.defect_lt
      hlegalA hbad hsize hsparse
  let hlen : (toRow v.row).bands.length=7 := by
    simpa only [toRow,List.length_map] using hp.length
  have hmatch : ∀ d ∈ Finset.Icc 1 s.D, ∀ b : CrossBandCredit208.Band,
      (ActualCleanupEval208.At (toRow v.row) hlen b).T=s.T d b ∧
      (ActualCleanupEval208.At (toRow v.row) hlen b).E=s.E d b ∧
      (ActualCleanupEval208.At (toRow v.row) hlen b).U=s.U d b ∧
      CleanupEval208.block (ActualCleanupEval208.At (toRow v.row) hlen b) d=s.B d b := by
    intro d hd b
    rw [←ActualUnitLayer208.evalData_at hp.length b]
    have hh := hmap d b
    rw [hdata b] at hh
    exact ⟨hh.1.symm,hh.2.1.symm,hh.2.2.1.symm,hh.2.2.2.symm⟩
  have hDn : s.D ≤ v.steps := by
    rw [hsD,hp.steps]
    exact Nat.div_le_div_right hhi
  have hsub : s.F ⊆ F := by
    intro S hS
    rw [hsF] at hS
    exact hAF (Finset.mem_filter.mp hS).1
  have hlegal : Legal (Ground s.N) F := by simpa only [hsN] using hlegalF
  have hb := FullSurplusFamily65968.actual_family_bound hvalid (toRow v.row) hlen hf hDn hmatch
    (by change 0 < v.row.grid; rw [hp.grid]; decide) hp.low_pos
    (by simpa only [hsN,toRow] using hlo) (by simpa only [hsN,toRow] using hhi)
    (by change s.e ≤ v.row.i; exact hse.le) hlegal hsub hA₀ hW hlight
  have hr := mul_le_mul_of_nonneg_left hresidual (sq_nonneg (N : ℝ))
  simp only [hsN,hsM,hse,hsF,toRow,toTotals,hp.grid,Nat.cast_ofNat] at hb
  dsimp only [Upper]
  nlinarith only [hb,hr]

#print axioms actual_near_bound
end
end JSP233.FullSurplusLayer65968
