module

public import Erdos272.Resources.ActualUnitLayer208
public import Erdos272.Arithmetic.N80470.CleanupFacts80470
public import Erdos272.Arithmetic.N80470.ResidualRows80470
public import Erdos272.Resources.N80470.RowSources80470
public import Erdos272.Resources.N80470.WitnessActualLayer80470
public import Erdos272.Counting.N80470.WitnessHighFacts80470
public import Erdos272.Counting.N80470.WitnessHighSound80470

@[expose] public section

namespace JSP233.Layer80470
open StarCompletion APGeometry DenseDeletion40 NearAP36 SevenFamily208 SourceCertified208 SourceBridge208 IntrinsicTriples208 CrossBandCredit208 CrossBandCredit208.System CleanupMachineSound208 ActualUnitRecipe208 UnitRecipeStatic208 CleanupRows80470 RowStatic291012
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option maxRecDepth 200000

def Facts (k : ℕ) : Prop := CleanupEval208.ChunkFacts (toRow (data k).row) 1 (data k).steps
  (toTotals (data k).total)

def recipe {N k ell : ℕ} {psi : ℕ → ℝ} {A : Finset (Finset ℤ)} (hk : k < 20)
    (hN : N ≤ (data k).row.high) (hlegal : Legal (Ground N) A)
    (hpot : psi (ell+1) = ((data k).potential : ℝ)) (hf : Facts k) :
    ActualUnitCut291012.CutRecipe N (data k).memberFloor (data k).row.i ell 12 psi A where
  data := evalData (data k).row
  M_le := fun b => ((RowGeometry80470.parameters hk).bands b).1
  E_le := fun b => ((RowGeometry80470.parameters hk).bands b).2.1
  TU := fun b => ((RowGeometry80470.parameters hk).bands b).2.2
  cover := fun _ hn hs => RowGeometry291012.cover (RowGeometry80470.parameters hk) hN hn hs
  physical := by
    intro d hd b
    have hp := RowGeometry80470.parameters hk
    have hDn : N/((data k).memberFloor-(data k).row.i) ≤ (data k).steps := by
      rw [hp.steps]
      exact Nat.div_le_div_right hN
    have hg := CleanupRowBounds208.good_Icc hf
      (Finset.mem_Icc.mpr ⟨(Finset.mem_Icc.mp hd).1, (Finset.mem_Icc.mp hd).2.trans hDn⟩)
    have hb := (CleanupEval208.step_good hg).1 (evalData (data k).row b) (evalData_mem hp.length b)
    exact ⟨hb.2.2.2.2.1, hb.2.2.2.2.2.1, hb.2.2.2.2.2.2.2.1⟩
  cut := by
    intro S hS b hlo _hhi
    have hSA := (Finset.mem_filter.mp hS).1
    have hc : S.card < 2^50 := by
      have hh := Finset.card_le_card (hlegal.1 S hSA)
      rw [ground_card] at hh
      exact lt_of_le_of_lt (hh.trans hN) (RowGeometry80470.parameters hk).high_bound
    by_contra hh
    have he : (evalData (data k).row b).E ≤ Defect S := by omega
    have hcard : 2 ≤ S.card := ((RowGeometry80470.parameters hk).member_two.trans
      (((RowGeometry80470.parameters hk).bands b).1.trans hlo))
    have hcap : N ≤ 2^18 := hN.trans (by
      interval_cases k <;> decide +kernel)
    have hsource := RowSources80470.actual_source hk b hcap (hlegal.1 S hSA) hcard hlo he
    have hnear := (Finset.mem_filter.mp hS).2
    rw [hpot] at hnear
    have hp : ((data k).potential : ℝ) ≤ (Pool S).card := by
      exact_mod_cast hsource
    exact (not_le_of_gt hnear) hp

def Witness (k : ℕ) : ℕ := WitnessHighSound80470.Witness k
def Upper (N k : ℕ) : ℝ :=
  WitnessActualLayer80470.Upper (data k) N (WitnessHighNumeric80470.data k).cap

theorem actual_upper {N k ell : ℕ} {psi : ℕ → ℝ} {A F : Finset (Finset ℤ)} {A₀ : Finset ℤ}
    (hk : k < 20) (hlo : (data k).row.low ≤ N) (hhi : N ≤ (data k).row.high)
    (hlegal : Legal (Ground N) A) (hbad : ∀ S ∈ A, ¬IsAP S)
    (hsize : ∀ S ∈ A, (data k).memberFloor ≤ S.card) (hsparse : ∀ S ∈ A, 12*S.card ≤ N)
    (hpot : psi (ell+1)=((data k).potential : ℝ))
    (hlegalF : Legal (Ground N) F) (hAF : A ⊆ F) (hA₀ : A₀ ∈ F)
    (hW : A₀.card ≤ Witness k) :
    ((PoolNear A psi ell).card : ℝ) ≤ Upper N k := by
  let p := recipe hk hhi hlegal hpot (CleanupFacts80470.all_facts hk)
  exact WitnessActualLayer80470.actual_near_bound (data k) (RowGeometry80470.parameters hk) p
    (by intro b; rfl) (CleanupFacts80470.all_facts hk) hlo hhi hlegal hbad hsize hsparse
    hlegalF hAF hA₀ hW (by
      exact (WitnessHighSound80470.high_value hk).le.trans
        (WitnessHighFacts80470.bound hk)) (ResidualRows80470.bound hk)

#print axioms actual_upper
end
end JSP233.Layer80470
