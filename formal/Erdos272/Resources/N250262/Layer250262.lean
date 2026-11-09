module

public import Erdos272.Arithmetic.N250262.CleanupFacts250262
public import Erdos272.Arithmetic.N250262.ResidualRows250262
public import Erdos272.Resources.N250262.RowSources250262
public import Erdos272.Resources.ActualUnitLayer208
public import Mathlib.Order.Interval.Finset.Nat

@[expose] public section

namespace JSP233.Layer250262
open StarCompletion APGeometry DenseDeletion40 NearAP36 SevenFamily208 SourceCertified208 SourceBridge208 IntrinsicTriples208
open CrossBandCredit208 CrossBandCredit208.System CleanupMachineSound208
open ActualUnitRecipe208 UnitRecipeStatic208 CleanupRows250262 RowStatic291012
open scoped Classical BigOperators
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option maxRecDepth 200000

def Facts (k : ℕ) : Prop := CleanupEval208.ChunkFacts (toRow (data k).row) 1 (data k).steps
  (toTotals (data k).total)

def recipe {N k ell : ℕ} {psi : ℕ → ℝ} {A : Finset (Finset ℤ)} (hk : k < 28)
    (hN : N ≤ (data k).row.high) (hlegal : Legal (Ground N) A)
    (hpot : psi (ell+1) = ((data k).potential : ℝ)) (hf : Facts k) :
    ActualUnitCut291012.CutRecipe N (data k).memberFloor (data k).row.i ell 12 psi A where
  data := evalData (data k).row
  M_le := fun b => ((RowGeometry250262.parameters hk).bands b).1
  E_le := fun b => ((RowGeometry250262.parameters hk).bands b).2.1
  TU := fun b => ((RowGeometry250262.parameters hk).bands b).2.2
  cover := fun _ hn hs => RowGeometry291012.cover (RowGeometry250262.parameters hk) hN hn hs
  physical := by
    intro d hd b
    have hp := RowGeometry250262.parameters hk
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
      exact lt_of_le_of_lt (hh.trans hN) (RowGeometry250262.parameters hk).high_bound
    by_contra hh
    have he : (evalData (data k).row b).E ≤ Defect S := by omega
    have hsource := RowSources250262.sources hk b S.card hlo hc
    have hcard : 2 ≤ S.card := ((RowGeometry250262.parameters hk).member_two.trans
      (((RowGeometry250262.parameters hk).bands b).1.trans hlo))
    have hlower := SourceBridge208.actual_source_of_defect hcard he
    have hnear := (Finset.mem_filter.mp hS).2
    rw [hpot] at hnear
    have hp : ((data k).potential : ℝ) ≤ (Pool S).card := by
      exact_mod_cast hsource.trans hlower
    exact (not_le_of_gt hnear) hp

def Upper (N k : ℕ) : ℝ := (N : ℝ)^2*(data k).residualUnits/1000000000000+
  (253/35 : ℝ)*N+(data k).total.light+(N : ℝ)*((data k).total.net/1000000000000 : ℝ)

theorem actual_upper {N k ell : ℕ} {psi : ℕ → ℝ} {A : Finset (Finset ℤ)} (hk : k < 28)
    (hlo : (data k).row.low ≤ N) (hhi : N ≤ (data k).row.high)
    (hlegal : Legal (Ground N) A) (hbad : ∀ S ∈ A, ¬IsAP S)
    (hsize : ∀ S ∈ A, (data k).memberFloor ≤ S.card) (hsparse : ∀ S ∈ A, 12*S.card ≤ N)
    (hpot : psi (ell+1) = ((data k).potential : ℝ)) :
    ((PoolNear A psi ell).card : ℝ) ≤ Upper (data k).row.high k := by
  have hp := RowGeometry250262.parameters hk
  have hf : Facts k := CleanupFacts250262.all_facts hk
  let p := recipe hk hhi hlegal hpot hf
  obtain ⟨s, hsN, hsD, hsM, hse, hsF, hmap, hv⟩ :=
    ActualUnitCut291012.actual_system p hp.member_two hp.defect_two hp.defect_lt
      hlegal hbad hsize hsparse
  let hlen : (toRow (data k).row).bands.length = 7 := by
    simpa only [toRow, List.length_map] using hp.length
  have hmatch : ∀ d ∈ Finset.Icc 1 s.D, ∀ b : Band,
      (ActualCleanupEval208.At (toRow (data k).row) hlen b).T = s.T d b ∧
      (ActualCleanupEval208.At (toRow (data k).row) hlen b).E = s.E d b ∧
      (ActualCleanupEval208.At (toRow (data k).row) hlen b).U = s.U d b ∧
      CleanupEval208.block (ActualCleanupEval208.At (toRow (data k).row) hlen b) d = s.B d b := by
    intro d _hd b
    rw [←ActualUnitLayer208.evalData_at hp.length b]
    exact ⟨(hmap d b).1.symm, (hmap d b).2.1.symm, (hmap d b).2.2.1.symm, (hmap d b).2.2.2.symm⟩
  have hDn : s.D ≤ (data k).steps := by
    rw [hsD, hp.steps]
    exact Nat.div_le_div_right hhi
  have hb := ActualCleanupEval208.actual_family_bound hv (toRow (data k).row) hlen hf hDn hmatch
    (by change 0 < (data k).row.grid; rw [hp.grid]; decide) hp.low_pos
    (by simpa only [hsN, toRow] using hlo) (by simpa only [hsN, toRow] using hhi)
    (by change s.e ≤ (data k).row.i; exact hse.le)
  have hr := mul_le_mul_of_nonneg_left (ResidualRows250262.bound hk) (sq_nonneg (N : ℝ))
  have hbill : ((PoolNear A psi ell).card : ℝ) ≤ Upper N k := by
    simp only [hsN, hsM, hse, hsF, toRow, toTotals, hp.grid, Nat.cast_ofNat] at hb
    dsimp only [Upper]
    nlinarith only [hb, hr]
  apply hbill.trans
  have hn : (N : ℝ) ≤ (data k).row.high := by exact_mod_cast hhi
  dsimp only [Upper]
  gcongr

#print axioms actual_upper
end
end JSP233.Layer250262
