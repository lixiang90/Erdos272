module

public import Erdos272.Resources.ActualUnitCut218
public import Erdos272.Arithmetic.Unit240Light218
public import Mathlib.Order.Interval.Finset.Nat

@[expose] public section

namespace JSP233.Unit240Family218
open StarCompletion APGeometry NearAP36 SourceCertified208
open SevenFamily208 UnitNearAggregate208 ActualUnitCut218 Unit240Rows218 Unit240Geometry218
open CrossBandCredit208 CrossBandCredit208.System CrossBandCleanup208
open ActualUnitRecipe208 UnitRecipeStatic208 CleanupMachineSound208
open Unit240Light218
open scoped Classical BigOperators
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 200000

def Facts (k : ℕ) : Prop := CleanupEval208.ChunkFacts (toRow (row k)) 1 (last k)
  (toTotals (expected k))

theorem fixed_parameters (k : ℕ) (hk : k<7) :
    (row k).grid=1000000000000 ∧ (row k).low=659000 ∧ (row k).high=705097 := by
  interval_cases k <;> decide +kernel

def recipe {A : Finset (Finset ℤ)} (k : ℕ) (hk : k<7)
    (hlegal : Legal (Ground 659912) A) (hsize : ∀S∈A,240≤S.card)
    (hf : Facts k) : CutRecipe 659912 240 (row k).i k Psi A where
  data:=evalData (row k)
  M_le:=fun b=>((parameters k hk).2.2.2.2.2 b).2.2.1
  E_le:=fun b=>((parameters k hk).2.2.2.2.2 b).2.2.2.1
  TU:=fun b=>((parameters k hk).2.2.2.2.2 b).2.2.2.2.1
  cover:=by
    intro n hn hs
    obtain ⟨b,hb⟩ := Unit240Geometry218.cover hn hs
    refine ⟨b,?_⟩
    have hp := (parameters k hk).2.2.2.2.2 b
    simpa only [evalData,toBand,hp.1,hp.2.1] using hb
  physical:=by
    intro d hd b
    have hDn : 659912/(240-(row k).i)≤last k := by
      rw [(parameters k hk).2.2.2.2.1]
      exact Nat.div_le_div_right (by decide : 659912≤705097)
    have hg := CleanupRowBounds208.good_Icc hf
      (Finset.mem_Icc.mpr ⟨(Finset.mem_Icc.mp hd).1,(Finset.mem_Icc.mp hd).2.trans hDn⟩)
    have hb := (CleanupEval208.step_good hg).1 (evalData (row k) b)
      (evalData_mem (parameters k hk).1 b)
    rcases hb with ⟨h1,h2,h3,h4,h5,h6,h7,h8,h9⟩
    exact ⟨h5,h6,h8⟩
  cut:=by
    intro S hS b hlo hhi
    have hSA := (Finset.mem_filter.mp hS).1
    have hc : S.card<2^50 := by
      have hh := Finset.card_le_card (hlegal.1 S hSA)
      rw [ground_card] at hh
      omega
    exact Unit240Geometry218.actual_cut hk hS (hsize S hSA) hc b hlo

def Bill (k : ℕ) : ℝ :=
  (659912 : ℝ)^2*ResidualAggregate208.Price (row k).i (ResidualTwoCensus208.H 240)+
  (253/35 : ℝ)*659912+(light k : ℝ)+(659912 : ℝ)*((expected k).net/1000000000000 : ℝ)

def Upper (k : ℕ) : ℝ :=
  (659912 : ℝ)^2*(units k : ℝ)/1000000000000+
  (253/35 : ℝ)*659912+(light k : ℝ)+(659912 : ℝ)*((expected k).net/1000000000000 : ℝ)

theorem actual_bill {A : Finset (Finset ℤ)} (k : ℕ) (hk : k<7)
    (hlegal : Legal (Ground 659912) A) (hbad : ∀S∈A,¬IsAP S)
    (hsize : ∀S∈A,240≤S.card) (hsparse : ∀S∈A,11*S.card≤659912)
    (hf : Facts k) : ((PoolNear A Psi k).card : ℝ)≤Bill k := by
  have hp := parameters k hk
  have hx := fixed_parameters k hk
  let p:=recipe k hk hlegal hsize hf
  obtain ⟨s,hsN,hsD,hsM,hse,hsF,hmap,hv⟩ :=
    ActualUnitCut218.actual_system p (by decide : 2≤240) hp.2.1 hp.2.2.1
      hlegal hbad hsize hsparse
  let hlen : (toRow (row k)).bands.length=7 := by
    simpa only [toRow,List.length_map] using hp.1
  have hmatch : ∀d∈Finset.Icc 1 s.D,∀b : Band,
      (ActualCleanupEval208.At (toRow (row k)) hlen b).T=s.T d b ∧
      (ActualCleanupEval208.At (toRow (row k)) hlen b).E=s.E d b ∧
      (ActualCleanupEval208.At (toRow (row k)) hlen b).U=s.U d b ∧
      CleanupEval208.block (ActualCleanupEval208.At (toRow (row k)) hlen b) d=s.B d b := by
    intro d hd b
    rw [←ActualUnitLayer208.evalData_at hp.1 b]
    exact ⟨(hmap d b).1.symm,(hmap d b).2.1.symm,(hmap d b).2.2.1.symm,(hmap d b).2.2.2.symm⟩
  have hDn : s.D≤last k := by
    rw [hsD,hp.2.2.2.2.1]
    exact Nat.div_le_div_right (by decide : 659912≤705097)
  have hlight : (∑d∈Finset.Icc 1 s.D,∑b : Band,LightCap216.PieceLight s 659912 d b)≤light k := by
    have hmatchL : ∀d b,LightCap216.PieceLight s 659912 d b=LightAt k d b := by
      intro d b
      simp only [LightCap216.PieceLight,(hmap d b).1,(hmap d b).2.1,
        (hmap d b).2.2.1,(hmap d b).2.2.2]
      rfl
    simp_rw [hmatchL]
    apply (Finset.sum_le_sum_of_subset_of_nonneg
      (show Finset.Icc 1 s.D⊆Finset.Icc 1 (last k) from fun d hd=>
        Finset.mem_Icc.mpr ⟨(Finset.mem_Icc.mp hd).1,(Finset.mem_Icc.mp hd).2.trans hDn⟩)
      (by intros;exact Nat.zero_le _)).trans
    exact (light_exact k hk).le
  have hb := LightCap216.actual_family_bound_cap hv (toRow (row k)) hlen hf hDn hmatch
    (by change 0<(row k).grid;rw [hx.1];decide)
    (by change 0<(row k).low;rw [hx.2.1];decide)
    (by change (row k).low≤s.N;rw [hx.2.1,hsN];decide)
    (by change s.N≤(row k).high;rw [hsN,hx.2.2];decide)
    (by change s.e≤(row k).i;exact hse.le)
    hsN.le hlight
  simpa only [Bill,hsN,hsM,hse,hsF,toRow,toTotals,hx.1,Nat.cast_ofNat] using hb

theorem bill_upper (k : ℕ) (hk : k<7) : Bill k≤Upper k := by
  have h := mul_le_mul_of_nonneg_left (residual_bound k hk) (show (0 : ℝ)≤659912^2 by positivity)
  dsimp only [Bill,Upper]
  nlinarith only [h]

theorem actual_upper {A : Finset (Finset ℤ)} (k : ℕ) (hk : k<7)
    (hlegal : Legal (Ground 659912) A) (hbad : ∀S∈A,¬IsAP S)
    (hsize : ∀S∈A,240≤S.card) (hsparse : ∀S∈A,11*S.card≤659912)
    (hf : Facts k) : ((PoolNear A Psi k).card : ℝ)≤Upper k :=
  (actual_bill k hk hlegal hbad hsize hsparse hf).trans (bill_upper k hk)

#print axioms fixed_parameters
#print axioms recipe
#print axioms actual_bill
#print axioms bill_upper
#print axioms actual_upper
end
end JSP233.Unit240Family218
