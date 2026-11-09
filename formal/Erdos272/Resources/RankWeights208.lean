module

public import Erdos272.Resources.RankSlots208
public import Mathlib.Algebra.BigOperators.Ring.Finset

@[expose] public section

/-! The total length of all rank-r gaps is at most r(N-1). -/
namespace JSP233.RankWeights208
open StarCompletion RankSlots208 TriangularWeights208
open scoped Classical BigOperators
noncomputable section
set_option maxHeartbeats 0

def gap (S : Finset ℤ) (r i : ℕ) : ℕ := (point S (i+r)-point S i).toNat

theorem gap_cast {S : Finset ℤ} {r i : ℕ} (hr : 0 < r) (hi : i+r < S.card) :
    (gap S r i : ℤ) = point S (i+r)-point S i := by
  apply Int.toNat_of_nonneg
  have hh := point_strict (by omega : i < i+r) hi
  omega

theorem telescope (f : ℕ → ℤ) (n : ℕ) :
    (∑ i ∈ Finset.range n, (f (i+1)-f i)) = f n-f 0 := by
  induction n with
  | zero => simp
  | succ n ih => rw [Finset.sum_range_succ, ih]; ring

theorem wide_telescope (f : ℕ → ℤ) (r i : ℕ) :
    f (i+r)-f i = ∑ j ∈ Finset.range r, (f (i+j+1)-f (i+j)) := by
  have hh := telescope (fun j => f (i+j)) r
  simpa only [Nat.add_assoc, Nat.add_zero] using hh.symm

theorem gap_sum_bound {N : ℕ} {S : Finset ℤ} {r : ℕ}
    (hS : S ⊆ Ground N) (hr : 0 < r) (hrs : r < S.card) :
    (∑ i ∈ Finset.range (S.card-r), (gap S r i : ℤ)) ≤ (r : ℤ)*((N : ℤ)-1) := by
  have hmain : (∑ i ∈ Finset.range (S.card-r), (gap S r i : ℤ)) =
      ∑ j ∈ Finset.range r, (point S (S.card-r+j)-point S j) := by
    calc
      _ = ∑ i ∈ Finset.range (S.card-r),
          ∑ j ∈ Finset.range r, (point S (i+j+1)-point S (i+j)) := by
        apply Finset.sum_congr rfl
        intro i hi
        rw [gap_cast hr (by have := Finset.mem_range.mp hi; omega), wide_telescope]
      _ = ∑ j ∈ Finset.range r,
          ∑ i ∈ Finset.range (S.card-r), (point S (i+j+1)-point S (i+j)) := Finset.sum_comm
      _ = _ := by
        apply Finset.sum_congr rfl
        intro j hj
        have hh := telescope (fun i => point S (i+j)) (S.card-r)
        simpa only [show ∀ i : ℕ, i+1+j = i+j+1 by omega, Nat.zero_add] using hh
  rw [hmain]
  calc
    _ ≤ ∑ _j ∈ Finset.range r, ((N : ℤ)-1) := by
      apply Finset.sum_le_sum
      intro j hj
      have hjr := Finset.mem_range.mp hj
      have hlo := (mem_ground N _).mp (hS (point_mem (by omega : j < S.card)))
      have hhi := (mem_ground N _).mp
        (hS (point_mem (by omega : S.card-r+j < S.card)))
      omega
    _ = _ := by simp; ring

theorem rank_weight_lower {N : ℕ} {S : Finset ℤ} {r : ℕ} {t : ℝ}
    (hN : 2 ≤ N) (hS : S ⊆ Ground N) (hr : 0 < r) (hrs : r < S.card)
    (ht : 0 ≤ t) :
    max ((S.card : ℝ)-r-r*t) 0 ≤ ∑ i ∈ Finset.range (S.card-r),
      Weight (t/((N : ℝ)-1)) (gap S r i) := by
  let u : ℝ := t/((N : ℝ)-1)
  have hNp : (0 : ℝ) < (N : ℝ)-1 := by
    have hh : (2 : ℝ) ≤ N := by exact_mod_cast hN
    linarith only [hh]
  have hu : 0 ≤ u := div_nonneg ht hNp.le
  have hsum : (∑ i ∈ Finset.range (S.card-r), (gap S r i : ℝ)) ≤
      (r : ℝ)*((N : ℝ)-1) := by exact_mod_cast gap_sum_bound hS hr hrs
  have hm := mul_le_mul_of_nonneg_left hsum hu
  have hc : u*((r : ℝ)*((N : ℝ)-1)) = r*t := by
    dsimp only [u]
    field_simp [ne_of_gt hNp]
  have hl : ∑ i ∈ Finset.range (S.card-r), (1-u*(gap S r i : ℝ)) ≤
      ∑ i ∈ Finset.range (S.card-r), Weight u (gap S r i) := by
    exact Finset.sum_le_sum (fun i _ => le_max_left _ _)
  simp only [Finset.sum_sub_distrib, Finset.sum_const, Finset.card_range, nsmul_eq_mul,
    mul_one, ← Finset.mul_sum] at hl
  have hcast : ((S.card-r : ℕ) : ℝ) = (S.card : ℝ)-r := Nat.cast_sub (by omega)
  rw [hc] at hm
  apply max_le
  · change (S.card : ℝ)-r-r*t ≤ ∑ i ∈ Finset.range (S.card-r), Weight u (gap S r i)
    linarith only [hm, hl, hcast]
  · apply Finset.sum_nonneg
    intro i _
    exact weight_nonneg _ _

#print axioms gap_sum_bound
#print axioms rank_weight_lower
end
end JSP233.RankWeights208
