module

public import Erdos272.Arithmetic.Unit240Rows218
public import Erdos272.Resources.ActualUnitLayer208
public import Erdos272.Arithmetic.ResidualCeil208
public import Mathlib.Order.Interval.Finset.Nat
public import Mathlib.Algebra.BigOperators.Ring.Finset

@[expose] public section

namespace JSP233.Unit240Geometry218
open StarCompletion APGeometry NearAP36 SourceBridge208 SourceCertified208 SourcePrefixSpecs208
open SevenFamily208 UnitNearAggregate208 UnitRecipeStatic208 Unit240Rows218
open scoped Classical BigOperators
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 200000

def Lower (b : Fin 7) : ℕ := [240,338,484,726,1210,2420,7744].getD b.val 0

def Check (k : ℕ) : Prop :=
  (row k).bands.length=7 ∧ 2≤(row k).i ∧ (row k).i<240 ∧
  (row k).i=SourceCut216.Height (Index (k+1)) ∧
  last k=705097/(240-(row k).i) ∧
  ∀b : Fin 7,
    (data (row k) b).T=Lower b ∧ (data (row k) b).U=upper242 b ∧
    240≤(data (row k) b).T ∧ (data (row k) b).E≤(row k).i ∧
    (data (row k) b).T<(data (row k) b).U ∧
    (b=0 → (data (row k) b).E=SourceCut216.Height (Index (k+1))) ∧
    (b≠0 → rowStart (source242 b)=(data (row k) b).T ∧
      floorAt row242 (Index (k+1))≤floorAt (source242 b) (data (row k) b).E)

instance (k : ℕ) : Decidable (Check k) := by unfold Check;infer_instance

theorem checked : (List.range 7).all (fun k=>decide (Check k))=true := by decide +kernel

theorem parameters (k : ℕ) (hk : k<7) : Check k :=
  of_decide_eq_true (List.all_eq_true.mp checked k (List.mem_range.mpr hk))

theorem cover {n : ℕ} (hlow : 240≤n) (hsparse : 11*n≤659912) :
    ∃b : Fin 7,Lower b≤n ∧ n<upper242 b := by
  by_cases h0 : n<338
  · exact ⟨0,by norm_num [Lower,upper242];exact ⟨hlow,h0⟩⟩
  by_cases h1 : n<484
  · exact ⟨1,by norm_num [Lower,upper242];omega⟩
  by_cases h2 : n<726
  · exact ⟨2,by norm_num [Lower,upper242];omega⟩
  by_cases h3 : n<1210
  · exact ⟨3,by norm_num [Lower,upper242];omega⟩
  by_cases h4 : n<2420
  · exact ⟨4,by norm_num [Lower,upper242];omega⟩
  by_cases h5 : n<7744
  · exact ⟨5,by norm_num [Lower,upper242];omega⟩
  exact ⟨6,by norm_num [Lower,upper242];omega⟩

theorem actual_cut {A : Finset (Finset ℤ)} {S : Finset ℤ} {k : ℕ}
    (hk : k<7) (hS : S∈PoolNear A Psi k) (hsize : 240≤S.card)
    (hcard : S.card<2^50) (b : Fin 7) (hlo : (data (row k) b).T≤S.card) :
    Defect S<(data (row k) b).E := by
  have hp := parameters k hk
  by_cases hb : b=0
  · have he := (hp.2.2.2.2.2 b).2.2.2.2.2.1 hb
    rw [he]
    apply SourceCut216.actual_pool_cut hsize hcard (Nat.min_le_right _ _)
    exact (Finset.mem_filter.mp hS).2
  · have hs := (hp.2.2.2.2.2 b).2.2.2.2.2.2 hb
    have hsource : Psi (k+1)≤(floorAt (source242 b) (data (row k) b).E : ℝ) := by
      change (floorAt row242 (Index (k+1)) : ℝ)≤_
      exact_mod_cast hs.2
    exact (DeficiencyCuts208.actual_unit_cut (source242 b) hS
      (by rw [hs.1];exact hlo) hcard hsource).trans_le (min_le_left _ _)

def LightAt (k d : ℕ) (b : Fin 7) : ℕ :=
  let v:=data (row k) b
  if v.E≤1 then 0 else
    CleanupMachine208.Closed 659912 d v.T v.E (CleanupMachine208.block v d)
      (v.U+CleanupMachine208.block v d-3)

def LightSum (k : ℕ) : ℕ := ∑d∈Finset.Icc 1 (last k),∑b : Fin 7,LightAt k d b

def LightRun (k start : ℕ) : ℕ→ℕ
  | 0 => 0
  | n+1 => LightRun k start n + ∑b : Fin 7,LightAt k (start+n) b

theorem light_run_sum (k start len : ℕ) :
    LightRun k start len=∑n∈Finset.range len,∑b : Fin 7,LightAt k (start+n) b := by
  induction len with
  | zero => simp [LightRun]
  | succ n ih => simp only [LightRun,Finset.sum_range_succ,ih]

def ResidualCheck (k : ℕ) : Bool := ResidualCeil208.Check 240 (row k).i (units k)
theorem checked_residual : (List.range 7).all ResidualCheck=true := by decide +kernel

theorem residual_bound (k : ℕ) (hk : k<7) :
    ResidualAggregate208.Price (row k).i (ResidualTwoCensus208.H 240)≤
      (units k : ℝ)/1000000000000 := by
  have hc := ResidualCeil208.check_sound (List.all_eq_true.mp checked_residual k (List.mem_range.mpr hk))
  have he := (parameters k hk).2.1
  norm_num only [ResidualCeil208.Grid,Nat.cast_pow,Nat.cast_ofNat] at hc
  simpa only [ResidualCheck,ResidualCeil208.B,if_pos he] using hc

#print axioms checked
#print axioms parameters
#print axioms cover
#print axioms actual_cut
#print axioms light_run_sum
#print axioms checked_residual
#print axioms residual_bound
end
end JSP233.Unit240Geometry218
