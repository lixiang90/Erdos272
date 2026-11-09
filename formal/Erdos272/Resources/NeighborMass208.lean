module

public import Erdos272.Resources.RankWeights208
public import Mathlib.Algebra.BigOperators.Ring.Finset
public import Mathlib.Order.Interval.Finset.Nat

@[expose] public section

/-! Three genuine rank supplies pay one actual weighted physical slot pool. -/
namespace JSP233.NeighborMass208
open StarCompletion SourceBridge208 PairEnvelope208 PairRanks208 NeighborSupply208
open RankSlots208 RankWeights208 TriangularWeights208
open scoped Classical BigOperators
noncomputable section
set_option maxHeartbeats 0

def Supply (S : Finset ℤ) (r : ℕ) : ℕ :=
  if r=1 then Defect S else if r=2 then (3*Defect S-S.card)/2 else (5*Defect S-2*S.card)/3

theorem point_supply {S : Finset ℤ} {i r : ℕ} (hr : r ∈ Finset.Icc 1 3)
    (hi : i+r < S.card) :
    Supply S r ≤ (IntrinsicPoints S (point S i) (point S (i+r))).card := by
  obtain ⟨hrlo, hrhi⟩ := Finset.mem_Icc.mp hr
  have hRank := actual_rank (by omega : 0 < r) hi
  have ha := point_mem (S := S) (i := i) (by omega)
  have hb := point_mem hi
  have hab := point_strict (i := i) (j := i+r) (by omega) hi
  interval_cases r
  · simpa [Supply] using rank_one_supply ha hb hab (by omega)
  · simpa [Supply] using
      rank_two_supply_floor ha hb hab (by omega)
  · simpa [Supply] using
      rank_three_supply_floor ha hb hab (by omega)

theorem pairs_sum (S : Finset ℤ) (k : ℕ) (f : ℕ × ℕ → ℝ) :
    (∑ p ∈ Pairs S k, f p) =
      ∑ r ∈ Finset.Icc 1 k, ∑ i ∈ Finset.range (S.card-r), f (r,i) := by
  rw [Pairs, Finset.sum_filter, Finset.product_eq_sprod, Finset.sum_product]
  apply Finset.sum_congr rfl
  intro r hr
  rw [← Finset.sum_filter]
  have he : (Finset.range S.card).filter (fun i => i+r < S.card) = Finset.range (S.card-r) := by
    ext i
    simp only [Finset.mem_filter, Finset.mem_range]
    omega
  rw [he]

theorem input_mass (S : Finset ℤ) (k : ℕ) (u : ℝ) :
    (∑ z ∈ Inputs S k, Weight u (code S z).1) =
      ∑ r ∈ Finset.Icc 1 k, ∑ i ∈ Finset.range (S.card-r),
        ((IntrinsicPoints S (point S i) (point S (i+r))).card : ℝ) * Weight u (gap S r i) := by
  rw [Inputs, Finset.sum_sigma]
  calc
    _ = ∑ p ∈ Pairs S k,
        ((IntrinsicPoints S (point S p.2) (point S (p.2+p.1))).card : ℝ) *
          Weight u (gap S p.1 p.2) := by
      apply Finset.sum_congr rfl
      intro p hp
      simp only [code, gap, Finset.sum_const, nsmul_eq_mul]
    _ = _ := pairs_sum S k _

theorem actual_rank_mass {N : ℕ} {S : Finset ℤ} {t : ℝ}
    (hN : 2 ≤ N) (hS : S ⊆ Ground N) (hs : 4 ≤ S.card) (ht : 0 ≤ t) :
    (∑ r ∈ Finset.Icc 1 3, (Supply S r : ℝ)*max ((S.card : ℝ)-r-r*t) 0) ≤
      NeighborSlots208.Mass N (t/((N : ℝ)-1)) S := by
  let u : ℝ := t/((N : ℝ)-1)
  apply le_trans (b := ∑ z ∈ Inputs S 3, Weight u (code S z).1)
  · rw [input_mass]
    apply Finset.sum_le_sum
    intro r hr
    have hrs := Finset.mem_Icc.mp hr
    have hw := rank_weight_lower hN hS (by omega : 0 < r) (by omega : r < S.card) ht
    calc
      _ ≤ (Supply S r : ℝ) * ∑ i ∈ Finset.range (S.card-r), Weight u (gap S r i) :=
        mul_le_mul_of_nonneg_left hw (by positivity)
      _ = ∑ i ∈ Finset.range (S.card-r), (Supply S r : ℝ)*Weight u (gap S r i) := Finset.mul_sum _ _ _
      _ ≤ _ := by
        apply Finset.sum_le_sum
        intro i hi
        have hsup : (Supply S r : ℝ) ≤ (IntrinsicPoints S (point S i) (point S (i+r))).card := by
          exact_mod_cast point_supply hr (by have := Finset.mem_range.mp hi; omega)
        exact mul_le_mul_of_nonneg_right hsup (weight_nonneg _ _)
  · exact input_mass_le hS u

def Q (s e : ℝ) (t : ℝ) : ℝ :=
  e*(s-1-t) + max (3*e-s-1) 0/2*max (s-2-2*t) 0 +
    max (5*e-2*s-2) 0/3*max (s-3-3*t) 0

/-- Full local source bound, with the conservative -1 and -2 offsets. -/
theorem actual_Q_mass {N : ℕ} {S : Finset ℤ} {t : ℝ}
    (hN : 2 ≤ N) (hS : S ⊆ Ground N) (hs : 4 ≤ S.card) (ht : 0 ≤ t) :
    Q S.card (Defect S) t ≤ NeighborSlots208.Mass N (t/((N : ℝ)-1)) S := by
  have hm := actual_rank_mass hN hS hs ht
  have h2nat : 3*Defect S ≤ S.card+1+2*((3*Defect S-S.card)/2) := by omega
  have h3nat : 5*Defect S ≤ 2*S.card+2+3*((5*Defect S-2*S.card)/3) := by omega
  have h2real : (3 : ℝ)*Defect S-(S.card : ℝ)-1 ≤ 2*((3*Defect S-S.card)/2 : ℕ) := by
    have hh : (3 : ℝ)*Defect S ≤ (S.card : ℝ)+1+2*((3*Defect S-S.card)/2 : ℕ) := by
      exact_mod_cast h2nat
    linarith only [hh]
  have h3real : (5 : ℝ)*Defect S-2*(S.card : ℝ)-2 ≤ 3*((5*Defect S-2*S.card)/3 : ℕ) := by
    have hh : (5 : ℝ)*Defect S ≤ 2*(S.card : ℝ)+2+3*((5*Defect S-2*S.card)/3 : ℕ) := by
      exact_mod_cast h3nat
    linarith only [hh]
  have h2 : max ((3 : ℝ)*Defect S-S.card-1) 0/2 ≤ ((3*Defect S-S.card)/2 : ℕ) := by
    have hh := max_le h2real (by positivity : (0 : ℝ) ≤ 2*((3*Defect S-S.card)/2 : ℕ))
    linarith only [hh]
  have h3 : max ((5 : ℝ)*Defect S-2*S.card-2) 0/3 ≤ ((5*Defect S-2*S.card)/3 : ℕ) := by
    have hh := max_le h3real (by positivity : (0 : ℝ) ≤ 3*((5*Defect S-2*S.card)/3 : ℕ))
    linarith only [hh]
  have hb1 := mul_le_mul_of_nonneg_left (le_max_left ((S.card : ℝ)-1-t) 0)
    (show (0 : ℝ) ≤ Defect S by positivity)
  have hb2 := mul_le_mul_of_nonneg_right h2 (le_max_right ((S.card : ℝ)-2-2*t) 0)
  have hb3 := mul_le_mul_of_nonneg_right h3 (le_max_right ((S.card : ℝ)-3-3*t) 0)
  have he : (Finset.Icc 1 3 : Finset ℕ) = {1,2,3} := by decide
  rw [he] at hm
  norm_num [Supply] at hm
  unfold Q
  linarith only [hm, hb1, hb2, hb3]

#print axioms actual_rank_mass
#print axioms actual_Q_mass
end
end JSP233.NeighborMass208
