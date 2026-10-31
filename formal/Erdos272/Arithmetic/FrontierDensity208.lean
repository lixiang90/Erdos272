import Erdos272.Arithmetic.CoprimeDensity52
import Mathlib.Tactic

/-! A finite reciprocal-square certificate. Only the first 1000 terms are
computed; finite telescoping controls the entire interval up to 1670000. -/
namespace JSP233.FrontierDensity208
open CoprimeDensity52
open scoped Classical BigOperators
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000

def Rho : ℝ := 500000000/822467033

def Grid (n : ℕ) : ℕ := ∑ d ∈ Finset.Icc 1 n, 1000000000000000/(d^2)

theorem grid_check : Grid 1000 = 1643934566681076 := by decide +kernel

theorem grid_bounds (n : ℕ) :
    (Grid n : ℝ) ≤ 1000000000000000*reciprocalSquareSum n ∧
    1000000000000000*reciprocalSquareSum n ≤ (Grid n : ℝ)+n := by
  have hlo : ∀ d ∈ Finset.Icc 1 n,
      ((1000000000000000/(d^2) : ℕ) : ℝ) ≤ 1000000000000000*((d : ℝ)^2)⁻¹ := by
    intro d hd
    have hh := Nat.cast_div_le (α := ℝ) (m := 1000000000000000) (n := d^2)
    simpa only [Nat.cast_ofNat, Nat.cast_pow, div_eq_mul_inv] using hh
  have hhi : ∀ d ∈ Finset.Icc 1 n,
      1000000000000000*((d : ℝ)^2)⁻¹ ≤ ((1000000000000000/(d^2) : ℕ) : ℝ)+1 := by
    intro d hd
    have hdpos : 0 < d^2 := pow_pos (Finset.mem_Icc.mp hd).1 _
    have hh := (TotientFloor29.nat_div_bounds 1000000000000000 (d^2) hdpos).2
    simpa only [Nat.cast_ofNat, Nat.cast_pow, div_eq_mul_inv] using hh
  have hl := Finset.sum_le_sum hlo
  have hu := Finset.sum_le_sum hhi
  simp only [Grid, Nat.cast_sum, Finset.sum_add_distrib, Finset.sum_const,
    Nat.card_Icc, Nat.add_sub_cancel, nsmul_eq_mul, mul_one,
    ← Finset.mul_sum, reciprocalSquareSum] at hl hu ⊢
  exact ⟨hl,hu⟩

def Upper (n : ℕ) : ℝ := reciprocalSquareSum n+1/(n : ℝ)
def Lower (n : ℕ) : ℝ := reciprocalSquareSum n+1/(n : ℝ)-1/(2*(n : ℝ)^2)

theorem upper_antitone {k n : ℕ} (hk : 1 ≤ k) (hkn : k ≤ n) :
    Upper n ≤ Upper k := by
  have hs : reciprocalSquareSum n = reciprocalSquareSum k+
      ∑ d ∈ Finset.Ioc k n, ((d : ℝ)^2)⁻¹ := by
    have he : Finset.Icc 1 n = Finset.Icc 1 k ∪ Finset.Ioc k n := by
      ext d
      simp only [Finset.mem_union, Finset.mem_Icc, Finset.mem_Ioc]
      omega
    have hd : Disjoint (Finset.Icc 1 k) (Finset.Ioc k n) := by
      apply Finset.disjoint_left.mpr
      intro d h1 h2
      have ha := Finset.mem_Icc.mp h1
      have hb := Finset.mem_Ioc.mp h2
      omega
    rw [reciprocalSquareSum,he,Finset.sum_union hd]
    rfl
  have ht := sum_Ioc_inv_sq_le_sub (α := ℝ) (k := k) (by omega) hkn
  dsimp only [Upper]
  rw [hs]
  simp only [one_div]
  linarith only [ht]

theorem lower_step {n : ℕ} (hn : 1 ≤ n) : Lower n ≤ Lower (n+1) := by
  have hnR : (0 : ℝ) < n := by exact_mod_cast (show 0<n by omega)
  have hn1 : (0 : ℝ) < n+1 := by positivity
  have hs : reciprocalSquareSum (n+1) = reciprocalSquareSum n + (((n+1 : ℕ) : ℝ)^2)⁻¹ := by
    exact Finset.sum_Icc_succ_top (by omega) _
  have he : Lower (n+1)-Lower n = 1/(2*(n : ℝ)^2*((n : ℝ)+1)^2) := by
    dsimp only [Lower]
    rw [hs]
    push_cast
    field_simp
    ring
  have hp : (0 : ℝ) ≤ 1/(2*(n : ℝ)^2*((n : ℝ)+1)^2) := by positivity
  linarith only [he,hp]

theorem lower_monotone {k n : ℕ} (hk : 1 ≤ k) (hkn : k ≤ n) : Lower k ≤ Lower n := by
  induction n, hkn using Nat.le_induction with
  | base => exact le_rfl
  | succ n hkn ih => exact ih.trans (lower_step (hk.trans hkn))

theorem lower_le_upper (n : ℕ) : Lower n ≤ Upper n := by
  have hp : (0 : ℝ) ≤ 1/(2*(n : ℝ)^2) := by positivity
  dsimp only [Lower,Upper]
  linarith only [hp]

theorem rho_bounds : (200/329 : ℝ) ≤ Rho ∧ Rho ≤ 1 := by norm_num [Rho]

theorem actual_square_lower {L : ℕ} (hL : 1 ≤ L) :
    1/Rho-reciprocalSquareSum L ≤ 1/(L : ℝ) := by
  have hg := (grid_bounds 1000).1
  rw [grid_check] at hg
  have hnum : 1/Rho ≤ Lower 1000 := by
    dsimp only [Lower,Rho]
    norm_num at hg ⊢
    linarith only [hg]
  have hl : Lower 1000 ≤ Upper L := by
    by_cases hLo : L ≤ 1000
    · exact (lower_le_upper 1000).trans (upper_antitone hL hLo)
    · exact (lower_monotone (by norm_num : 1≤1000) (by omega : 1000≤L)).trans
        (lower_le_upper L)
  dsimp only [Upper] at hl
  linarith only [hnum,hl]

theorem actual_square_upper {L : ℕ} (hhigh : L ≤ 1670000) :
    reciprocalSquareSum L ≤ 1/Rho := by
  have hg := (grid_bounds 1000).2
  rw [grid_check] at hg
  by_cases hL : L ≤ 1000
  · have hs : reciprocalSquareSum L ≤ reciprocalSquareSum 1000 := by
      apply Finset.sum_le_sum_of_subset_of_nonneg
      · intro d hd
        exact Finset.mem_Icc.mpr ⟨(Finset.mem_Icc.mp hd).1,(Finset.mem_Icc.mp hd).2.trans hL⟩
      · intro d _ _
        positivity
    dsimp only [Rho]
    norm_num at hg ⊢
    linarith only [hg,hs]
  · have hA := upper_antitone (by norm_num : 1≤1000) (by omega : 1000≤L)
    have hLpos : (0 : ℝ) < L := by exact_mod_cast (show 0<L by omega)
    have hrecip : (1/1670000 : ℝ) ≤ 1/(L : ℝ) :=
      one_div_le_one_div_of_le hLpos (by exact_mod_cast hhigh)
    simp only [one_div] at hrecip
    dsimp only [Upper,Rho] at hA ⊢
    norm_num at hg hA ⊢
    linarith only [hg,hA,hrecip]

#print axioms grid_check
#print axioms actual_square_lower
#print axioms actual_square_upper
end
end JSP233.FrontierDensity208
