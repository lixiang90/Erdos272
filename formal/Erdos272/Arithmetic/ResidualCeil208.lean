import Erdos272.Resources.NearResidual208

namespace JSP233.ResidualCeil208
open ResidualAggregate208 ResidualTwoCensus208 ResidualCensus208 StepCensus208 ResidualSpan208
open scoped Classical BigOperators
noncomputable section
set_option maxHeartbeats 0

def Scale : ℕ := 10^30
def Grid : ℕ := 10^12
def InvUpper (n : ℕ) : ℕ := 1+(Scale-1)/n
def Factor (e b : ℕ) : ℕ := if b=e then e-1 else b*(b-1)

def Upper (M e : ℕ) : ℕ := ∑ b ∈ Finset.Icc 2 e, ∑ p ∈ Classes,
  PeriodMass p*(InvUpper ((M-b)*Factor e b)+InvUpper (Span (M-b) b p*Factor e b))

def B (M e : ℕ) : ℝ := if 2 ≤ e then Price e (H M) else 0

theorem inv_upper {n : ℕ} (hn : 0 < n) :
    1/(n : ℝ) ≤ (InvUpper n : ℝ)/(Scale : ℝ) := by
  have hs : 0 < Scale := by norm_num [Scale]
  have hmul : Scale ≤ InvUpper n*n := by
    have hh := Nat.lt_mul_div_succ (Scale-1) hn
    unfold InvUpper
    calc
      Scale = (Scale-1)+1 := by omega
      _ ≤ n*((Scale-1)/n+1) := by omega
      _ = (1+(Scale-1)/n)*n := by ring
  have hR : (Scale : ℝ) ≤ (InvUpper n : ℝ)*n := by exact_mod_cast hmul
  apply (div_le_div_iff₀ (by positivity : (0 : ℝ)<n) (by exact_mod_cast hs)).mpr
  simpa only [one_mul] using hR

theorem factor_pos {e b : ℕ} (he : 2 ≤ e) (hb : b ∈ Finset.Icc 2 e) : 0 < Factor e b := by
  obtain ⟨hb2,hbe⟩ := Finset.mem_Icc.mp hb
  unfold Factor
  split_ifs
  · omega
  · exact Nat.mul_pos (by omega) (by omega)

theorem price_as_sum (A : ℕ → ℝ) {e : ℕ} (he : 2 ≤ e) :
    Price e A=∑ b ∈ Finset.Icc 2 e, A b/(Factor e b : ℝ) := by
  have hset : Finset.Icc 2 e=insert e (Finset.Ico 2 e) := by
    ext b
    simp only [Finset.mem_Icc,Finset.mem_insert,Finset.mem_Ico]
    omega
  rw [hset,Finset.sum_insert (by simp)]
  unfold Price
  simp only [Factor,if_true]
  congr 1
  apply Finset.sum_congr rfl
  intro b hb
  have hne : b ≠ e := by have := (Finset.mem_Ico.mp hb).2; omega
  simp only [if_neg hne,Nat.cast_mul,Nat.cast_sub (show 1 ≤ b by have := (Finset.mem_Ico.mp hb).1; omega),Nat.cast_one]

theorem h_factor (M e b : ℕ) :
    H M b/(Factor e b : ℝ)=∑ p ∈ Classes, (PeriodMass p : ℝ)/210*
      (1/(((M-b)*Factor e b : ℕ) : ℝ)+1/((Span (M-b) b p*Factor e b : ℕ) : ℝ)) := by
  unfold H
  rw [Finset.sum_div]
  apply Finset.sum_congr rfl
  intro p hp
  unfold Rho
  simp only [Nat.cast_mul,div_eq_mul_inv,mul_inv_rev]
  ring

theorem upper_sound {M e : ℕ} (he : 2 ≤ e) (heM : e < M) :
    Price e (H M) ≤ (Upper M e : ℝ)/(210*(Scale : ℝ)) := by
  rw [price_as_sum _ he]
  simp_rw [h_factor]
  calc
    _ ≤ ∑ b ∈ Finset.Icc 2 e, ∑ p ∈ Classes, (PeriodMass p : ℝ)/210*
        ((InvUpper ((M-b)*Factor e b) : ℝ)/Scale+
          (InvUpper (Span (M-b) b p*Factor e b) : ℝ)/Scale) := by
      apply Finset.sum_le_sum
      intro b hb
      have ha : 0 < M-b := by have := (Finset.mem_Icc.mp hb).2; omega
      have hf := factor_pos he hb
      apply Finset.sum_le_sum
      intro p hp
      have hs : 0 < Span (M-b) b p := lt_of_lt_of_le ha (span_ge _ _ _)
      exact mul_le_mul_of_nonneg_left
        (add_le_add (inv_upper (Nat.mul_pos ha hf)) (inv_upper (Nat.mul_pos hs hf))) (by positivity)
    _ = _ := by
      unfold Upper
      push_cast
      rw [Finset.sum_div]
      apply Finset.sum_congr rfl
      intro b hb
      rw [Finset.sum_div]
      apply Finset.sum_congr rfl
      intro p hp
      simp only [div_eq_mul_inv,mul_inv_rev]
      ring

def Check (M e u : ℕ) : Bool := decide (e < M ∧ Grid*Upper M e ≤ 210*Scale*u)

theorem check_sound {M e u : ℕ} (hcheck : Check M e u=true) :
    B M e ≤ (u : ℝ)/(Grid : ℝ) := by
  have hc : e < M ∧ Grid*Upper M e ≤ 210*Scale*u := of_decide_eq_true hcheck
  unfold B
  split_ifs with he
  · apply (upper_sound he hc.1).trans
    have hR : (Grid : ℝ)*(Upper M e : ℝ) ≤ 210*(Scale : ℝ)*u := by exact_mod_cast hc.2
    apply (div_le_div_iff₀ (by norm_num [Scale] : (0 : ℝ)<210*(Scale : ℝ))
      (by norm_num [Grid] : (0 : ℝ)<(Grid : ℝ))).mpr
    nlinarith only [hR]
  · positivity

#print axioms upper_sound
#print axioms check_sound
end
end JSP233.ResidualCeil208
