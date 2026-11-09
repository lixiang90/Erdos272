module

public import Erdos272.Arithmetic.StepWeightShape208
public import Erdos272.Arithmetic.PrefixAbel208
public import Erdos272.Resources.SourceBridge208
public import Mathlib.Algebra.Order.Floor.Semifield
public import Mathlib.Order.Interval.Finset.Nat
public import Mathlib.Algebra.BigOperators.Intervals
public import Mathlib.Algebra.BigOperators.Ring.Finset
public import Mathlib.Algebra.Order.Archimedean.Real.Basic

@[expose] public section

/-! The finite totient frontier controls all actual AP-cover triples by Abel. -/
namespace JSP233.UniformAbel208
open StarCompletion SourceBridge208 PureSource208 APInterval208 TripleCodes208 IntrinsicTriples208
open UniformSourceCore208 StepWeightShape208 PrefixAbel208
open scoped Classical BigOperators
noncomputable section
set_option maxHeartbeats 0

theorem physical_weight (s q : ℕ) (hq : 0 < q) :
    w s q = (q : ℝ)*(intervalMultiplicity s q : ℝ) := by
  let D := s/q
  have hlo : q*D ≤ s := Nat.mul_div_le s q
  have hhi : s ≤ q*(D+1) := (Nat.lt_mul_div_succ s hq).le
  have hi := interval_window (by omega : 1 ≤ q) hlo hhi
  have hiR : 2*(intervalMultiplicity s q : ℝ)+(q : ℝ)*(D : ℝ)*((D : ℝ)+1) = 2*(D : ℝ)*s := by
    exact_mod_cast hi
  have hStep : Step (s : ℝ) (q : ℝ)=D := Nat.floor_div_eq_div s q
  unfold w
  rw [hStep]
  calc
    _ = (q : ℝ)*((D : ℝ)*s-(q : ℝ)*D*((D : ℝ)+1)/2) := by ring
    _ = _ := by congr 1; linarith only [hiR]

theorem physical_weight_one (s : ℕ) : w s 1 = (s : ℝ)*((s : ℝ)-1)/2 := by
  unfold w Step
  simp only [div_one, Nat.floor_natCast]
  ring

theorem ratio_weight (s q : ℕ) (hq : 0 < q) :
    (Nat.totient q : ℝ)/(q : ℝ)*w s q = (Nat.totient q : ℝ)*(intervalMultiplicity s q : ℝ) := by
  rw [physical_weight s q hq]
  have hq0 : (q : ℝ) ≠ 0 := by positivity
  field_simp

theorem shifted_sum (f : ℕ → ℝ) (n : ℕ) :
    (∑ i ∈ Finset.range n, f (i+1)) = ∑ q ∈ Finset.Icc 1 n, f q := by
  induction n with
  | zero => simp
  | succ n ih => rw [Finset.sum_range_succ, Finset.sum_Icc_succ_top (by omega), ih]

def F (t : ℕ) : ℝ := ∑ n ∈ Finset.Icc 1 t, (Nat.totient n : ℝ)/n

theorem weighted_frontier (s m : ℕ) (hs : 0 < s) (hm : 2 ≤ m) (delta C : ℝ)
    (hF : ∀ k, 1 ≤ k → k < m → F k ≤ delta*k+C) :
    (∑ q ∈ Finset.Ico 2 m, (Nat.totient q : ℝ)*(intervalMultiplicity s q : ℝ)) ≤
      delta*(∑ q ∈ Finset.Ico 1 m, w s q)+(C-1)*w s 1 := by
  let a : ℕ → ℝ := fun i => (Nat.totient (i+1) : ℝ)/(i+1 : ℕ)
  let weights : ℕ → ℝ := fun i => w s (i+1 : ℕ)
  have hprefix : ∀ k, 1 ≤ k → k ≤ m-1 → Prefix a k ≤ delta*k+C := by
    intro k hk hkm
    have he : Prefix a k = F k := shifted_sum (fun q => (Nat.totient q : ℝ)/q) k
    rw [he]
    exact hF k hk (by omega)
  have hw0 : ∀ i < m-1, 0 ≤ weights i := by
    intro i hi
    exact w_nonneg (by positivity : (0 : ℝ) ≤ s) (by positivity)
  have hwdec : ∀ i, i+1 < m-1 → weights (i+1) ≤ weights i := by
    intro i hi
    apply w_antitone (by exact_mod_cast hs : (0 : ℝ) < s) (by positivity)
    exact_mod_cast Nat.le_succ (i+1)
  have hh := weighted_upper a weights (m-1) (by omega) delta C hprefix hw0 hwdec
  have hi : Finset.Icc 1 (m-1)=Finset.Ico 1 m := by
    ext q
    simp only [Finset.mem_Icc, Finset.mem_Ico]
    omega
  dsimp only [a, weights] at hh
  norm_num only [Nat.zero_add, Nat.cast_one] at hh
  rw [shifted_sum (fun q => ((Nat.totient q : ℝ)/q)*w s q) (m-1),
    shifted_sum (fun q => w s q) (m-1), hi] at hh
  have hsplit : Finset.Ico 1 m = insert 1 (Finset.Ico 2 m) := by
    ext q
    simp only [Finset.mem_Ico, Finset.mem_insert]
    omega
  have hnot : 1 ∉ Finset.Ico 2 m := by simp
  have heq : (∑ q ∈ Finset.Ico 1 m, ((Nat.totient q : ℝ)/q)*w s q) =
      w s 1+∑ q ∈ Finset.Ico 2 m, (Nat.totient q : ℝ)*(intervalMultiplicity s q : ℝ) := by
    rw [hsplit, Finset.sum_insert hnot]
    norm_num only [Nat.totient_one, Nat.cast_one, one_div, inv_one, one_mul]
    congr 1
    apply Finset.sum_congr rfl
    intro q hq
    exact ratio_weight s q (by have := (Finset.mem_Ico.mp hq).1; omega)
  rw [heq] at hh
  linarith only [hh]

theorem actual_intrinsic_frontier {S : Finset ℤ} (hs : 2 ≤ S.card) (delta C : ℝ)
    (hF : ∀ k, 1 ≤ k → k < MaxAPSize S → F k ≤ delta*k+C) :
    (S.card.choose 3 : ℝ) - delta*(∑ q ∈ Finset.Ico 1 (MaxAPSize S), w S.card q) -
      (C-1)*w S.card 1 ≤ (Pool S).card := by
  have hactual := actual_intrinsic_lower (S := S) (m := MaxAPSize S)
    (fun R hR hRS => AP_card_le_max hR hRS)
  have hactualR : (S.card.choose 3 : ℝ) ≤ (Pool S).card+
      ∑ q ∈ Finset.Ico 2 (MaxAPSize S), (Nat.totient q : ℝ)*(intervalMultiplicity S.card q : ℝ) := by
    exact_mod_cast hactual
  have hb := weighted_frontier S.card (MaxAPSize S) (by omega) (two_le_maxAPSize hs) delta C hF
  linarith only [hactualR, hb]

#print axioms physical_weight
#print axioms weighted_frontier
#print axioms actual_intrinsic_frontier
end
end JSP233.UniformAbel208
