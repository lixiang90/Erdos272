module

public import Erdos272.Foundation.ProofTactics
public import Mathlib.Data.Real.Basic
public import Mathlib.Data.Nat.Sqrt

@[expose] public section

/-! Uniform square-root parameters for the complete Near/Far/root costs.

Only numerical functions occur.  No family, cardinality bound, global upper
theorem, or recovery hypothesis is assumed.  The actual geometric interpretation
of Mass/Cutoff/G is supplied independently by the round-113 family modules.
-/
namespace JSP233.UniformScale113
noncomputable section

def lower : ℕ := 74320000
def budget : ℝ := 4437 / 50000
def beta : ℝ := 21 / 242
def Mass (k : ℕ) : ℕ := k * (2*k-1)
def Cutoff (k : ℕ) : ℕ := 19*k/12
def Nu (k : ℕ) : ℝ := (2303/200 : ℝ)/k
def G (n k : ℕ) : ℝ := 2*(n : ℝ)/((Mass k : ℝ)*(Cutoff k : ℝ))
def Eta (n j : ℕ) : ℝ := (7/2 : ℝ)*(j : ℝ)^2/n
def rootA (n k : ℕ) : ℝ := 6*(k : ℝ)/n
def root (n j k : ℕ) : ℝ :=
  max (rootA n k + Nu k + G n k)
    (beta + rootA n k*(Nu k+G n k)/beta) + Eta n j
def whole (n j k : ℕ) : ℝ := Nu k+G n k+Eta n j
def direct (n k c : ℕ) : ℝ := (c : ℝ)*(3*(k : ℝ))/n
def selectedK (n : ℕ) : ℕ := Nat.sqrt (493*n/50000)

def numeratorFactor : ℝ := (50000/493 : ℝ)*(857/856 : ℝ)^2
def massFactor : ℝ := 1711/856
def cutoffFactor : ℝ := 16253/10272
def farCoefficient : ℝ := 2*numeratorFactor/(massFactor*cutoffFactor)
def wholeCoefficient : ℝ := 2303/200+farCoefficient
def aCoefficient : ℝ := 1479/25000
def etaLimit : ℝ := (7/2 : ℝ)*49^2/74320000
def bLimit : ℝ := wholeCoefficient/856
def aLimit : ℝ := aCoefficient/856
def rootLimit : ℝ := max (aLimit+bLimit) (beta+aLimit*bLimit/beta)+etaLimit

theorem selected_bounds {n : ℕ} (hn : lower ≤ n) :
    856 ≤ selectedK n ∧ 50000*(selectedK n)^2 ≤ 493*n ∧
      493*n < 50000*(selectedK n+1)^2 := by
  have hK : 856 ≤ selectedK n := by
    apply Nat.le_sqrt'.mpr
    apply (Nat.le_div_iff_mul_le (by norm_num : 0 < 50000)).mpr
    norm_num [lower] at hn ⊢
    nlinarith
  have hsq := Nat.sqrt_le' (493*n/50000)
  have hlo := (Nat.le_div_iff_mul_le (by norm_num : 0 < 50000)).mp hsq
  have hsu := Nat.lt_succ_sqrt' (493*n/50000)
  have hhi := (Nat.div_lt_iff_lt_mul (by norm_num : 0 < 50000)).mp hsu
  exact ⟨hK, by simpa [selectedK, mul_comm] using hlo,
    by simpa [selectedK, mul_comm] using hhi⟩

theorem mass_cast {k : ℕ} (hk : 1 ≤ k) :
    (Mass k : ℝ) = (k : ℝ)*(2*(k : ℝ)-1) := by
  simp only [Mass, Nat.cast_mul, Nat.cast_sub (by omega : 1 ≤ 2*k),
    Nat.cast_ofNat, Nat.cast_one]

theorem cutoff_lower {k : ℕ} (hk : 856 ≤ k) :
    cutoffFactor*(k : ℝ) ≤ Cutoff k := by
  have hm := Nat.mod_lt (19*k) (by decide : 0 < 12)
  have he := Nat.mod_add_div (19*k) 12
  have ht : 19*k ≤ 12*Cutoff k+11 := by dsimp [Cutoff]; omega
  have htR : 19*(k : ℝ) ≤ 12*(Cutoff k : ℝ)+11 := by exact_mod_cast ht
  have hkR : (856 : ℝ) ≤ k := by exact_mod_cast hk
  norm_num [cutoffFactor]
  nlinarith

theorem mass_lower {k : ℕ} (hk : 856 ≤ k) :
    massFactor*(k : ℝ)^2 ≤ Mass k := by
  have hkR : (856 : ℝ) ≤ k := by exact_mod_cast hk
  rw [mass_cast (by omega)]
  norm_num [massFactor]
  nlinarith

theorem numerator_upper {n k : ℕ} (hk : 856 ≤ k)
    (hshell : 493*n < 50000*(k+1)^2) :
    (n : ℝ) ≤ numeratorFactor*(k : ℝ)^2 := by
  have hkR : (856 : ℝ) ≤ k := by exact_mod_cast hk
  have hsR : 493*(n : ℝ) < 50000*((k : ℝ)+1)^2 := by exact_mod_cast hshell
  have hr : (k : ℝ)+1 ≤ (857/856 : ℝ)*(k : ℝ) := by nlinarith
  have hr2 : ((k : ℝ)+1)^2 ≤ ((857/856 : ℝ)*(k : ℝ))^2 :=
    (sq_le_sq₀ (by positivity) (by positivity)).mpr hr
  dsimp [numeratorFactor]
  nlinarith

theorem far_coefficient_bound {n k : ℕ} (hk : 856 ≤ k)
    (hshell : 493*n < 50000*(k+1)^2) :
    G n k ≤ farCoefficient/(k : ℝ) := by
  have hkR : (0 : ℝ) < k := by exact_mod_cast (show 0 < k by omega)
  have hn := numerator_upper hk hshell
  have hm := mass_lower hk
  have ht := cutoff_lower hk
  have hmf : (0 : ℝ) < massFactor := by norm_num [massFactor]
  have htf : (0 : ℝ) < cutoffFactor := by norm_num [cutoffFactor]
  have hden : massFactor*cutoffFactor*(k : ℝ)^3 ≤ (Mass k : ℝ)*(Cutoff k : ℝ) := by
    have hp := mul_le_mul hm ht (show (0 : ℝ) ≤ cutoffFactor*k by positivity)
      (show (0 : ℝ) ≤ (Mass k : ℝ) by positivity)
    nlinarith only [hp]
  dsimp [G]
  calc
    _ ≤ 2*(numeratorFactor*(k : ℝ)^2)/((Mass k : ℝ)*(Cutoff k : ℝ)) :=
      div_le_div_of_nonneg_right (by linarith) (by positivity)
    _ ≤ 2*(numeratorFactor*(k : ℝ)^2)/(massFactor*cutoffFactor*(k : ℝ)^3) :=
      div_le_div_of_nonneg_left (by norm_num [numeratorFactor]) (by positivity) hden
    _ = _ := by
      dsimp [farCoefficient, numeratorFactor, massFactor, cutoffFactor]
      field_simp

theorem whole_coefficient_positive : 0 ≤ wholeCoefficient := by
  norm_num [wholeCoefficient, farCoefficient, numeratorFactor, massFactor, cutoffFactor]

theorem b_uniform {n k : ℕ} (hk : 856 ≤ k)
    (hshell : 493*n < 50000*(k+1)^2) : Nu k+G n k ≤ bLimit := by
  have hf := far_coefficient_bound hk hshell
  have hkR : (856 : ℝ) ≤ k := by exact_mod_cast hk
  have hd := div_le_div_of_nonneg_left whole_coefficient_positive (by norm_num : (0 : ℝ) < 856) hkR
  dsimp [Nu, bLimit, wholeCoefficient] at *
  rw [add_div] at hd
  linarith

theorem a_uniform {n k : ℕ} (hk : 856 ≤ k) (hlo : 50000*k^2 ≤ 493*n) :
    rootA n k ≤ aLimit := by
  have hkR : (0 : ℝ) < k := by exact_mod_cast (show 0 < k by omega)
  have hkR0 : (856 : ℝ) ≤ k := by exact_mod_cast hk
  have hloR : (50000/493 : ℝ)*(k : ℝ)^2 ≤ n := by
    have hh : 50000*(k : ℝ)^2 ≤ 493*(n : ℝ) := by exact_mod_cast hlo
    nlinarith
  have ha : rootA n k ≤ aCoefficient/(k : ℝ) := by
    dsimp [rootA]
    calc
      _ ≤ 6*(k : ℝ)/((50000/493 : ℝ)*(k : ℝ)^2) :=
        div_le_div_of_nonneg_left (by positivity) (by positivity) hloR
      _ = _ := by dsimp [aCoefficient]; field_simp; norm_num
  exact ha.trans (div_le_div_of_nonneg_left (by norm_num [aCoefficient]) (by norm_num) hkR0)

theorem eta_uniform {n j : ℕ} (hn : lower ≤ n) (hj : j ≤ 49) : Eta n j ≤ etaLimit := by
  have hnR : (74320000 : ℝ) ≤ n := by exact_mod_cast hn
  have hjR : (j : ℝ) ≤ 49 := by exact_mod_cast hj
  have hj0 : (0 : ℝ) ≤ j := by positivity
  dsimp [Eta, etaLimit]
  calc
    _ ≤ ((7/2 : ℝ)*49^2)/(n : ℝ) := div_le_div_of_nonneg_right (by nlinarith) (by positivity)
    _ ≤ _ := div_le_div_of_nonneg_left (by norm_num) (by norm_num) hnR

theorem exact_budget_prices :
    bLimit+etaLimit ≤ budget ∧ rootLimit ≤ budget ∧
    budget+1/500000 ≤ (71/800 : ℝ)-536/74320000 := by
  norm_num [budget, bLimit, etaLimit, rootLimit, aLimit, aCoefficient,
    wholeCoefficient, farCoefficient, numeratorFactor, massFactor, cutoffFactor, beta]

theorem whole_uniform {n j k : ℕ} (hn : lower ≤ n) (hj : j ≤ 49)
    (hk : 856 ≤ k) (hshell : 493*n < 50000*(k+1)^2) :
    whole n j k ≤ budget := by
  have hb := b_uniform hk hshell
  have he := eta_uniform hn hj
  dsimp [whole]
  linarith [exact_budget_prices.1]

theorem root_uniform {n j k : ℕ} (hn : lower ≤ n) (hj : j ≤ 49)
    (hk : 856 ≤ k) (hlo : 50000*k^2 ≤ 493*n)
    (hshell : 493*n < 50000*(k+1)^2) : root n j k ≤ budget := by
  have ha := a_uniform hk hlo
  have hb := b_uniform hk hshell
  have hb0 : 0 ≤ Nu k+G n k := by dsimp [Nu, G]; positivity
  have hab : rootA n k*(Nu k+G n k) ≤ aLimit*bLimit := by
    calc
      _ ≤ aLimit*(Nu k+G n k) := mul_le_mul_of_nonneg_right ha hb0
      _ ≤ _ := mul_le_mul_of_nonneg_left hb (by norm_num [aLimit, aCoefficient])
  have hq := div_le_div_of_nonneg_right hab (show (0 : ℝ) ≤ beta by norm_num [beta])
  have he := eta_uniform hn hj
  have hr : root n j k ≤ rootLimit := by
    dsimp [root, rootLimit]
    exact add_le_add (max_le_max (by linarith) (by linarith)) he
  exact hr.trans exact_budget_prices.2.1

theorem selected_direct {n : ℕ} (hn : lower ≤ n) :
    direct n (selectedK n) (3*selectedK n) ≤ budget := by
  have hs := (selected_bounds hn).2.1
  have hsR : 50000*(selectedK n : ℝ)^2 ≤ 493*(n : ℝ) := by exact_mod_cast hs
  have hnR : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by norm_num [lower] at hn; omega)
  dsimp [direct, budget]
  push_cast
  apply (div_le_iff₀ hnR).mpr
  nlinarith

def ParameterBudget (n j k d c : ℕ) : Prop :=
  1 ≤ d ∧ d ≤ k ∧ 3*d ≤ c ∧ c ≤ 3*k ∧ 3*k ≤ n ∧
    direct n k c ≤ budget ∧ whole n j k ≤ budget ∧
    whole n j d ≤ budget ∧ root n j k ≤ budget

theorem selected_parameters {n j : ℕ} (hn : lower ≤ n) (hj : j ≤ 49) :
    ParameterBudget n j (selectedK n) (selectedK n) (3*selectedK n) := by
  obtain ⟨hk, hlo, hhi⟩ := selected_bounds hn
  have hk2 : selectedK n ≤ (selectedK n)^2 := by nlinarith
  refine ⟨by omega, le_rfl, le_rfl, le_rfl, by nlinarith, selected_direct hn,
    whole_uniform hn hj hk hhi, whole_uniform hn hj hk hhi, root_uniform hn hj hk hlo hhi⟩

theorem exists_uniform_parameters {n j : ℕ} (hn : lower ≤ n) (hj : j ≤ 49) :
    ∃ k d c : ℕ, ParameterBudget n j k d c :=
  ⟨selectedK n, selectedK n, 3*selectedK n, selected_parameters hn hj⟩

theorem conservative_density_margin {n j : ℕ} (hn : lower ≤ n) (hj : j ≤ 49) :
    budget+1/500000 ≤ (71/800 : ℝ)-(487+(j : ℝ))/(n : ℝ) := by
  have hnR : (74320000 : ℝ) ≤ n := by exact_mod_cast hn
  have hjR : (j : ℝ) ≤ 49 := by exact_mod_cast hj
  have hdiv : (487+(j : ℝ))/(n : ℝ) ≤ (536 : ℝ)/74320000 := by
    calc
      _ ≤ (536 : ℝ)/(n : ℝ) := div_le_div_of_nonneg_right (by linarith) (by positivity)
      _ ≤ _ := div_le_div_of_nonneg_left (by norm_num) (by norm_num) hnR
  linarith [exact_budget_prices.2.2]

#print axioms selected_bounds
#print axioms mass_cast
#print axioms cutoff_lower
#print axioms mass_lower
#print axioms numerator_upper
#print axioms far_coefficient_bound
#print axioms whole_coefficient_positive
#print axioms b_uniform
#print axioms a_uniform
#print axioms eta_uniform
#print axioms exact_budget_prices
#print axioms whole_uniform
#print axioms root_uniform
#print axioms selected_direct
#print axioms selected_parameters
#print axioms exists_uniform_parameters
#print axioms conservative_density_margin
end
end JSP233.UniformScale113
