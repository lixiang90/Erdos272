module

public import Erdos272.Core.N200000.PairUnionSieve200000
public import Erdos272.Core.N200000.CoreCeil200000

@[expose] public section

/-! One unused prime slot pays the exceptional run interval. The full
union-bound core source is uniform in every actual outside denominator. -/
namespace JSP233.CoreUnionSource200000
open StarCompletion APGeometry SourceBridge208 IntrinsicTriples208
open IndexedCorePairs200000 PrimePairEvents200000 PairUnionSieve200000
open scoped Classical BigOperators
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 0

def AllPrimes (a : ℕ) : Finset ℕ := (Finset.range a).filter Nat.Prime

def Weight (a q : ℕ) : ℕ := ((a + q - 1) / q).choose 2

def UnitBound (a : ℕ) : ℕ := a.choose 2 - ∑ q ∈ AllPrimes a, Weight a q

theorem active_primes_subset (a h : ℕ) : Primes a h ⊆ AllPrimes a := by
  intro q hq
  obtain ⟨hr, hp, _hn⟩ := Finset.mem_filter.mp hq
  exact Finset.mem_filter.mpr ⟨hr, hp⟩

theorem ceil_mono_denominator {a p h : ℕ} (ha : 0 < a) (hp : 0 < p) (hh : 0 < h) (hph : p ≤ h) :
    (a + h - 1) / h ≤ (a + p - 1) / p := by
  rw [← CoreCeil200000.ceil_count ha hh, ← CoreCeil200000.ceil_count ha hp]
  exact Nat.add_le_add_right (Nat.div_le_div_left hph hp) 1

theorem ceil_le_one {a h : ℕ} (hh : 0 < h) (ha : a ≤ h) : (a + h - 1) / h ≤ 1 := by
  by_contra hn
  have htwo : 2 ≤ (a + h - 1) / h := by omega
  have hm := Nat.mul_le_mul_left h htwo
  have hd : h * ((a + h - 1) / h) ≤ a + h - 1 := Nat.mul_div_le _ _
  omega

theorem first_bound_ge_unit {a h : ℕ} (ha : 2 ≤ a) (hh : 0 < h) :
    UnitBound a ≤ FirstBound a h (ExceptionLength a h) := by
  by_cases hone : h = 1
  · subst h
    have he : Primes a 1 = AllPrimes a := by
      ext q
      constructor
      · intro hq
        exact active_primes_subset a 1 hq
      · intro hq
        obtain ⟨hr, hp⟩ := Finset.mem_filter.mp hq
        refine Finset.mem_filter.mpr ⟨hr, hp, ?_⟩
        intro hd
        have hqone := Nat.dvd_one.mp hd
        have htwo := hp.two_le
        omega
    simp [UnitBound, Weight, FirstBound, ExceptionLength, he]
  · let b := ExceptionLength a h
    let p := h.minFac
    have hp : p.Prime := Nat.minFac_prime hone
    have hpd : p ∣ h := Nat.minFac_dvd h
    have hph : p ≤ h := Nat.le_of_dvd hh hpd
    have hbceil : b ≤ (a + h - 1) / h := by
      dsimp only [b, ExceptionLength]
      rw [if_neg hone]
      exact min_le_right _ _
    have hfee : (∑ q ∈ Primes a h, (Weight a q - (b / q).choose 2)) ≤
        ∑ q ∈ Primes a h, Weight a q := Finset.sum_le_sum (fun _ _ => Nat.sub_le _ _)
    have htotal : (∑ q ∈ Primes a h, (Weight a q - (b / q).choose 2)) + b.choose 2 ≤
        ∑ q ∈ AllPrimes a, Weight a q := by
      by_cases hpa : p < a
      · have hpAll : p ∈ AllPrimes a := Finset.mem_filter.mpr ⟨Finset.mem_range.mpr hpa, hp⟩
        have hpNot : p ∉ Primes a h := by
          intro hmem
          exact (Finset.mem_filter.mp hmem).2.2 hpd
        have hInsert : insert p (Primes a h) ⊆ AllPrimes a :=
          Finset.insert_subset_iff.mpr ⟨hpAll, active_primes_subset a h⟩
        have hsum : (∑ q ∈ insert p (Primes a h), Weight a q) ≤ ∑ q ∈ AllPrimes a, Weight a q :=
          Finset.sum_le_sum_of_subset hInsert
        rw [Finset.sum_insert hpNot] at hsum
        have hb : b ≤ (a + p - 1) / p := hbceil.trans (ceil_mono_denominator (by omega) hp.pos hh hph)
        have hchoose := Nat.choose_le_choose 2 hb
        change b.choose 2 ≤ Weight a p at hchoose
        omega
      · have hah : a ≤ h := (by omega : a ≤ p).trans hph
        have hb : b ≤ 1 := hbceil.trans (ceil_le_one hh hah)
        have hbzero : b.choose 2 = 0 := Nat.choose_eq_zero_of_lt (by omega)
        have hsum : (∑ q ∈ Primes a h, Weight a q) ≤ ∑ q ∈ AllPrimes a, Weight a q :=
          Finset.sum_le_sum_of_subset (active_primes_subset a h)
        omega
    change a.choose 2 - (∑ q ∈ AllPrimes a, Weight a q) ≤
      a.choose 2 - b.choose 2 - ∑ q ∈ Primes a h, (Weight a q - (b / q).choose 2)
    omega

theorem actual_union_core_source {S : Finset ℤ} (hS : 2 ≤ S.card) :
    Defect S * UnitBound (MaxAPSize S) ≤ (Pool S).card := by
  apply actual_source_of_first_bound hS
  intro h hh
  exact first_bound_ge_unit (two_le_maxAPSize hS) hh

#print axioms active_primes_subset
#print axioms ceil_mono_denominator
#print axioms ceil_le_one
#print axioms first_bound_ge_unit
#print axioms actual_union_core_source
end
end JSP233.CoreUnionSource200000
