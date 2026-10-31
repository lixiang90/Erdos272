import Erdos272.Resources.SevenFamily208
import Erdos272.Resources.CrossBandMenu208

namespace JSP233.UnitNearAggregate208
open SevenFamily208 SevenPrices208 SourceCertified208
open CrossBandCredit208 CrossBandCredit208.System CrossBandCleanup208 CrossBandMenu208
open scoped Classical BigOperators
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 200000

def row242 : Fin 14 := ⟨0,by decide⟩
def row243 : Fin 14 := ⟨1,by decide⟩
def psi242 (i : ℕ) : ℝ := potential row242 i
def psi243 (i : ℕ) : ℝ := potential row243 i

theorem zero242 : floorAt row242 0=0 := by decide +kernel
theorem zero243 : floorAt row243 0=0 := by decide +kernel
theorem cap242 : floorAt row242 183=1446946 := by decide +kernel
theorem cap243 : floorAt row243 184=1468276 := by decide +kernel

theorem psi242_zero : psi242 0=0 := by norm_num [psi242,potential,zero242]
theorem psi243_zero : psi243 0=0 := by norm_num [psi243,potential,zero243]
theorem psi242_mono : Monotone psi242 := potential_monotone row242
theorem psi243_mono : Monotone psi243 := potential_monotone row243
theorem reciprocal242 : 6*G242*psi242 183=1 := by norm_num [G242,psi242,potential,cap242]
theorem reciprocal243 : 6*G243*psi243 184=1 := by norm_num [G243,psi243,potential,cap243]

def RawLayerCost (s : System) : ℝ :=
  (∑d∈Finset.Icc 1 s.D,∑b : Band,s.Light d b)+
  (s.N : ℝ)^2*ResidualAggregate208.Price s.e (ResidualTwoCensus208.H s.M)+
  (253/35 : ℝ)*s.N+
  ((∑d∈Finset.Icc 1 s.D,(∑b : Band,(s.Heavy d b).card)*
    (min s.N (∑b : Band,UnionBound s d b)+(s.e-1)) : ℕ) : ℝ)-
  (∑d∈Finset.Icc 1 s.D,∑b : Band,(s.T d b : ℝ)*(s.Heavy d b).card)

def LayerCost (s : System) : ℝ := if s.F=∅ then 0 else RawLayerCost s

theorem actual_layer_cost (s : System) (v : s.F=∅ ∨ Valid s) : (s.F.card : ℝ)≤LayerCost s := by
  by_cases hzero : s.F=∅
  · simp [LayerCost,hzero]
  · have hv : Valid s := v.resolve_left hzero
    have hh := actual_closed_near_payment s hv
    simp only [LayerCost,if_neg hzero,RawLayerCost]
    linarith only [hh]

/-- Only actual per-layer band data and an arithmetic bill aggregation are
external. The near-family cardinality bounds are derived internally. -/
theorem actual_unit_obligation {N cap : ℕ} {A : Finset (Finset ℤ)} {psi : ℕ→ℝ}
    {g u eta light : ℝ} (hpsi : Monotone psi) (hzero : psi 0=0) (hg : 0≤g)
    (hrecip : 6*g*psi cap=1) (frame : ℕ→System)
    (hvalid : ∀i∈Finset.range cap,(frame i).F=∅ ∨ Valid (frame i))
    (hfamily : ∀i∈Finset.range cap,(frame i).F=PoolNear A psi i)
    (harithmetic : 6*g*(∑i∈Finset.range cap,(psi (i+1)-psi i)*LayerCost (frame i))≤
      u*(N : ℝ)^2+eta*N+light) : UnitNearObligation N A g u eta light := by
  refine ⟨psi,cap,hpsi,hzero,hrecip,?_⟩
  have hsum : (∑i∈Finset.range cap,(psi (i+1)-psi i)*((PoolNear A psi i).card : ℝ))≤
      ∑i∈Finset.range cap,(psi (i+1)-psi i)*LayerCost (frame i) := by
    apply Finset.sum_le_sum
    intro i hi
    have hb := actual_layer_cost (frame i) (hvalid i hi)
    rw [hfamily i hi] at hb
    exact mul_le_mul_of_nonneg_left hb (sub_nonneg.mpr (hpsi (Nat.le_succ i)))
  exact (mul_le_mul_of_nonneg_left hsum (show 0≤6*g by positivity)).trans harithmetic

theorem actual_unit242 {N : ℕ} {A : Finset (Finset ℤ)} (frame : ℕ→System)
    (hvalid : ∀i∈Finset.range 183,(frame i).F=∅ ∨ Valid (frame i))
    (hfamily : ∀i∈Finset.range 183,(frame i).F=PoolNear A psi242 i)
    (harithmetic : 6*G242*(∑i∈Finset.range 183,(psi242 (i+1)-psi242 i)*LayerCost (frame i))≤
      U242*(N : ℝ)^2+Eta242*N+Light242) : UnitNearObligation N A G242 U242 Eta242 Light242 :=
  actual_unit_obligation psi242_mono psi242_zero (by norm_num [G242]) reciprocal242
    frame hvalid hfamily harithmetic

theorem actual_unit243 {N : ℕ} {A : Finset (Finset ℤ)} (frame : ℕ→System)
    (hvalid : ∀i∈Finset.range 184,(frame i).F=∅ ∨ Valid (frame i))
    (hfamily : ∀i∈Finset.range 184,(frame i).F=PoolNear A psi243 i)
    (harithmetic : 6*G243*(∑i∈Finset.range 184,(psi243 (i+1)-psi243 i)*LayerCost (frame i))≤
      U243*(N : ℝ)^2+Eta243*N+Light243) : UnitNearObligation N A G243 U243 Eta243 Light243 :=
  actual_unit_obligation psi243_mono psi243_zero (by norm_num [G243]) reciprocal243
    frame hvalid hfamily harithmetic

#print axioms cap242
#print axioms cap243
#print axioms actual_layer_cost
#print axioms actual_unit_obligation
#print axioms actual_unit242
#print axioms actual_unit243
end
end JSP233.UnitNearAggregate208
