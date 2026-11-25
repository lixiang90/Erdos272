module

public import Erdos272.Counting.N82427.ThreeFiveIndex82427
public import Erdos272.Core.N88404.DenseCore88404

@[expose] public section

namespace JSP233.ThreeFiveSource82427
open StarCompletion APGeometry SourceBridge208 IntrinsicTriples208
open IndexedCorePairs200000 ActualCorePairs200000 CoreUnionSource200000
open StarArithmetic130000 ThreeFiveArithmetic82427 ThreeFiveIndex82427
open scoped Classical BigOperators
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1000000

theorem index_source {a h l : ℕ} {ell : ℤ}
    (ha : 12≤a) (hh : 0<h) (hc : Int.gcd (h : ℤ) ell=1)
    (hu : (∑ q∈AllPrimes a, Weight a q)≤a.choose 2)
    (hlen : l+ExceptionLength a h≤a) :
    UnitBound a+Bonus CorrelatedSource118533.Primes a+ChordBonus a≤
      (GoodIndex a h ell (Finset.Ico l (l+ExceptionLength a h))).card := by
  by_cases hlarge : 45≤a
  · exact chord_index_bound hlarge hh hc hu hlen
  · have hg := chord_bonus_zero (show a<45 by omega)
    rw [hg, add_zero]
    let Q := CorrelatedSource118533.Primes.filter (fun q => q<a)
    have hsub : Q⊆CorrelatedSource118533.Primes := Finset.filter_subset _ _
    have hQ : Q⊆AllPrimes a := by
      intro q hq
      obtain ⟨hqQ, hqa⟩ := Finset.mem_filter.mp hq
      exact Finset.mem_filter.mpr ⟨Finset.mem_range.mpr hqa,
        (CorrelatedSource118533.primes_odd q hqQ).1⟩
    have hbonus : Bonus Q a=Bonus CorrelatedSource118533.Primes a :=
      bonus_filter (fun q hq => (CorrelatedSource118533.primes_odd q hq).1.pos)
    rw [← hbonus]
    exact StarCore130000.star_index_bound ha hh hc hu hQ
      (fun q hq => (CorrelatedSource118533.primes_odd q (hsub hq)).2)
      (reciprocal_subset hsub CorrelatedSource118533.reciprocal_cap) hlen

theorem actual_eight_chord_source {N : ℕ} {S : Finset ℤ}
    (hN : N≤2^18) (hground : S⊆Ground N) (hS : 2≤S.card)
    (ha : 12≤MaxAPSize S) :
    Defect S*(UnitBound (MaxAPSize S)+Bonus CorrelatedSource118533.Primes (MaxAPSize S)+
      ChordBonus (MaxAPSize S))≤(Pool S).card := by
  have hcard : S.card≤N := by simpa only [ground_card] using Finset.card_le_card hground
  have hmax : MaxAPSize S≤2^18 := (maxAPSize_le_card S).trans (hcard.trans hN)
  apply actual_defect_source_of_index_bound hS
  intro h hh ell hc l hlen
  exact index_source ha hh hc (StarActual158375.weights_le_choose ha hmax) hlen

theorem actual_core_price_plus_chord {N : ℕ} {S : Finset ℤ}
    (hN : N≤2^18) (hground : S⊆Ground N) (hS : 2≤S.card)
    (ha : 92≤MaxAPSize S) :
    (Defect S : ℝ)*(DenseCore88404.CorePrice (MaxAPSize S : ℝ)+
      (ChordBonus (MaxAPSize S) : ℝ))≤((Pool S).card : ℝ) := by
  have hcard : S.card≤N := by simpa only [ground_card] using Finset.card_le_card hground
  have hmax : MaxAPSize S≤2^18 := (maxAPSize_le_card S).trans (hcard.trans hN)
  have hprice := DenseCore88404.combined_quadratic ha hmax
  have hsource := actual_eight_chord_source hN hground hS (by omega : 12≤MaxAPSize S)
  have hm := mul_le_mul_of_nonneg_left
    (add_le_add_right hprice (ChordBonus (MaxAPSize S) : ℝ))
    (Nat.cast_nonneg (α := ℝ) (Defect S))
  have hsourceR : (Defect S : ℝ)*
      (UnitBound (MaxAPSize S)+Bonus CorrelatedSource118533.Primes (MaxAPSize S)+
        ChordBonus (MaxAPSize S) : ℕ)≤((Pool S).card : ℝ) := by exact_mod_cast hsource
  push_cast at hm hsourceR
  calc
    _ ≤(Defect S : ℝ)*((UnitBound (MaxAPSize S) : ℝ)+
        (Bonus CorrelatedSource118533.Primes (MaxAPSize S) : ℝ)+
        (ChordBonus (MaxAPSize S) : ℝ)) := by
      simpa only [add_assoc, add_left_comm, add_comm] using hm
    _ ≤_ := hsourceR

theorem actual_core_lower_price {N a₀ : ℕ} {S : Finset ℤ}
    (hN : N≤2^18) (hground : S⊆Ground N) (hS : 2≤S.card)
    (ha : 12≤MaxAPSize S) (hlower : a₀≤MaxAPSize S) :
    Defect S*(UnitFloorData158375.unitFloor a₀+
      Bonus CorrelatedSource118533.Primes a₀+ChordBonus a₀)≤(Pool S).card := by
  have hcard : S.card≤N := by simpa only [ground_card] using Finset.card_le_card hground
  have hmax : MaxAPSize S≤2^18 := (maxAPSize_le_card S).trans (hcard.trans hN)
  have hu := UnitFloor158375.uniform_unit_floor hlower hmax
  have hb := bonus_mono (Q := CorrelatedSource118533.Primes) hlower
  have hg := chord_bonus_mono hlower
  have hprice := Nat.add_le_add (Nat.add_le_add hu hb) hg
  exact (Nat.mul_le_mul_left (Defect S) hprice).trans
    (actual_eight_chord_source hN hground hS ha)

#print axioms index_source
#print axioms actual_eight_chord_source
#print axioms actual_core_price_plus_chord
#print axioms actual_core_lower_price
end
end JSP233.ThreeFiveSource82427
