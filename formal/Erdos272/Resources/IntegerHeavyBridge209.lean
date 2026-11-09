module

public import Erdos272.Arithmetic.IntegerUniformHeavyData209
public import Erdos272.Resources.FullBandLinear209
public import Mathlib.Order.Interval.Finset.Nat

@[expose] public section

namespace JSP233.IntegerHeavyBridge209
open StarCompletion APGeometry SevenFamily208
open CrossBandCredit208 CrossBandCredit208.System CrossBandCleanup208
open IntegerUniformProfiles209 IntegerUniformRows209 IntegerHighPrices209
open IntegerUniformHeavyData209
open scoped Classical BigOperators
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1800000
set_option maxRecDepth 200000

/-- The numeric rational bill is the coefficient of the actual full/middle
partition, including the supported right-middle charge. -/
theorem coefficient_cast (w : Fin 11) (k : ℕ) :
    (HeavyRat w k : ℝ)=FullBandLinear209.Coefficient (row w k).e
      (T w k) (E w k) (U w k) (IntegerUniformHeavyData209.B w k) (pairJ w k) := by
  unfold HeavyRat FullBandLinear209.Coefficient HeavyFiniteSums209.Coefficient
    CleanupIntegral209.Tangent
  simp only [Rat.cast_add,Rat.cast_mul,Rat.cast_sum,Rat.cast_div,Rat.cast_pow,
    Rat.cast_natCast,Rat.cast_ofNat,Rat.cast_one,Rat.cast_max,Nat.cast_max]
  rfl

theorem actual_heavy (w : Fin 11) (i : Fin (count w)) (s : System) (v : Valid s)
    (hN : 0<s.N) (he : s.e=(row w i.val).e)
    (hfields : ∀d∈Finset.Icc 1 s.D,∀b : Fin 7,
      s.T d b=(band (row w i.val) b).T ∧ s.E d b=(band (row w i.val) b).E ∧
      s.U d b=(band (row w i.val) b).U ∧ s.B d b=CleanupEval208.block (band (row w i.val) b) d) :
    FullBandCleanup209.CleanupTotal s+FullBandCleanup209.MiddleTotal s≤
      (heavyCeiling w i.val : ℝ)*s.N := by
  have hw:=IntegerUniformRows209.facts (W_mem w) (row_mem w i)
  have hET : ∀b : Fin 7,E w i.val b<T w i.val b :=
    fun b=>(IntegerUniformShape209.physical_domain w i b).1
  have hTU : ∀b : Fin 7,T w i.val b<U w i.val b :=
    fun b=>(hw.2.2.2.2.2.2.1 b).2.2.2.1
  have hB : ∀b : Fin 7,2≤IntegerUniformHeavyData209.B w i.val b := by
    intro b
    have hh:=(hw.2.2.2.2.2.2.1 b).2.2.2.2 2 (by simp)
    simpa only [IntegerUniformHeavyData209.B,blockPrime] using hh.1
  have hfixed : ∀d∈Finset.Icc 1 s.D,∀b : Fin 7,
      s.T d b=T w i.val b ∧ s.E d b=E w i.val b ∧
      s.U d b=U w i.val b ∧ s.B d b=IntegerUniformHeavyData209.B w i.val b := by
    intro d hd b
    obtain ⟨ht,he',hu,hb⟩:=hfields d hd b
    exact ⟨ht,he',hu,by simpa only [IntegerUniformShape209.block_constant,IntegerUniformHeavyData209.B] using hb⟩
  have hp:=FullBandLinear209.actual_linear s v (T w i.val) (E w i.val)
    (U w i.val) (IntegerUniformHeavyData209.B w i.val) (pairJ w i.val) hN hET hTU hB hfixed
  have hc : FullBandLinear209.Coefficient s.e (T w i.val) (E w i.val)
      (U w i.val) (IntegerUniformHeavyData209.B w i.val) (pairJ w i.val)≤(heavyCeiling w i.val : ℝ) := by
    rw [he,←coefficient_cast]
    exact bound w i
  have hm:=mul_le_mul_of_nonneg_left hc (Nat.cast_nonneg (α := ℝ) s.N)
  calc
    _≤(s.N : ℝ)*FullBandLinear209.Coefficient s.e (T w i.val) (E w i.val)
      (U w i.val) (IntegerUniformHeavyData209.B w i.val) (pairJ w i.val) := hp
    _≤(s.N : ℝ)*(heavyCeiling w i.val : ℝ) := hm
    _=_ := mul_comm _ _

#print axioms coefficient_cast
#print axioms actual_heavy
end
end JSP233.IntegerHeavyBridge209
