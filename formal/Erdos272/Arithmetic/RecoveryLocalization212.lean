module

public import Erdos272.Resources.ActualRecoveryChain208
public import Erdos272.Arithmetic.PrefixTable132

@[expose] public section
namespace JSP233.RecoveryLocalization212
open HarmonicAbel29 RecoveryPrefix208 PrefixState131 PrefixCert131 PrefixTable131
open scoped Classical BigOperators
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 200000
theorem state_99 : Valid grid 99 ⟨45951195728,45951200369,163666534192,163666534290,445732748617,445732770655,770026366836,473⟩ := by
  exact chunk_sound [⟨6,102565000,102565003,1010152545⟩,⟨6,101523713,101523716,1005037816⟩] (by decide) (by decide) PrefixTable131.state_97 (by decide +kernel)

def Div (j : ℕ) : ℝ := match j with
  | 0 => (193/10 : ℝ)
  | 1 => (97/5 : ℝ)
  | 2 => (341/10 : ℝ)
  | 3 => (342/10 : ℝ)
  | 4 => (137/4 : ℝ)
  | 5 => (494/10 : ℝ)
  | 6 => (99/2 : ℝ)
  | 7 => (50/1 : ℝ)
  | _ => 50

def Lower (j : ℕ) : ℝ := match j with
  | 0 => (7400262027/2500000000 : ℝ)
  | 1 => (14826363943/5000000000 : ℝ)
  | 2 => (35292970913/10000000000 : ℝ)
  | 3 => (3532225351/1000000000 : ℝ)
  | 4 => (3533686283/1000000000 : ℝ)
  | 5 => (38999501237/10000000000 : ℝ)
  | 6 => (487746549/125000000 : ℝ)
  | 7 => (19560113871/5000000000 : ℝ)
  | _ => (19560113871/5000000000 : ℝ)

def LocalLog (j : ℕ) : ℝ := LogCap-Lower j
def LocalCoeff (j : ℕ) : ℝ := 102/25+2*(LocalLog j+1)+FrontierSum208.Polynomial (LocalLog j)

theorem div_pos (j : ℕ) : 0<Div j := by
  unfold Div
  split <;> norm_num

theorem lower_log {j : ℕ} (hj : j≤7) : Lower j ≤ Real.log (Div j) := by
  interval_cases j
  · have hn := (PrefixLog131.log_bounds (by decide : 0<grid) PrefixTable132.state_193).1
    have hk := (PrefixLog131.log_bounds (by decide : 0<grid) PrefixTable131.state_10).2
    change Lower 0 ≤ Real.log ((193 : ℝ)/10)
    rw [Real.log_div (by norm_num) (by norm_num)]
    norm_num [Lower,grid] at hn hk ⊢
    linarith only [hn,hk]
  · have hn := (PrefixLog131.log_bounds (by decide : 0<grid) PrefixTable131.state_97).1
    have hk := (PrefixLog131.log_bounds (by decide : 0<grid) PrefixTable131.state_5).2
    change Lower 1 ≤ Real.log ((97 : ℝ)/5)
    rw [Real.log_div (by norm_num) (by norm_num)]
    norm_num [Lower,grid] at hn hk ⊢
    linarith only [hn,hk]
  · have hn := (PrefixLog131.log_bounds (by decide : 0<grid) PrefixTable131.state_341).1
    have hk := (PrefixLog131.log_bounds (by decide : 0<grid) PrefixTable131.state_10).2
    change Lower 2 ≤ Real.log ((341 : ℝ)/10)
    rw [Real.log_div (by norm_num) (by norm_num)]
    norm_num [Lower,grid] at hn hk ⊢
    linarith only [hn,hk]
  · have hn := (PrefixLog131.log_bounds (by decide : 0<grid) PrefixTable131.state_342).1
    have hk := (PrefixLog131.log_bounds (by decide : 0<grid) PrefixTable131.state_10).2
    change Lower 3 ≤ Real.log ((342 : ℝ)/10)
    rw [Real.log_div (by norm_num) (by norm_num)]
    norm_num [Lower,grid] at hn hk ⊢
    linarith only [hn,hk]
  · have hn := (PrefixLog131.log_bounds (by decide : 0<grid) RecoveryPrefix208.state_137).1
    have hk := (PrefixLog131.log_bounds (by decide : 0<grid) RecoveryPrefix208.state_4).2
    change Lower 4 ≤ Real.log ((137 : ℝ)/4)
    rw [Real.log_div (by norm_num) (by norm_num)]
    norm_num [Lower,grid] at hn hk ⊢
    linarith only [hn,hk]
  · have hn := (PrefixLog131.log_bounds (by decide : 0<grid) PrefixTable131.state_494).1
    have hk := (PrefixLog131.log_bounds (by decide : 0<grid) PrefixTable131.state_10).2
    change Lower 5 ≤ Real.log ((494 : ℝ)/10)
    rw [Real.log_div (by norm_num) (by norm_num)]
    norm_num [Lower,grid] at hn hk ⊢
    linarith only [hn,hk]
  · have hn := (PrefixLog131.log_bounds (by decide : 0<grid) state_99).1
    have hk := (PrefixLog131.log_bounds (by decide : 0<grid) PrefixTable131.state_2).2
    change Lower 6 ≤ Real.log ((99 : ℝ)/2)
    rw [Real.log_div (by norm_num) (by norm_num)]
    norm_num [Lower,grid] at hn hk ⊢
    linarith only [hn,hk]
  · have hn := (PrefixLog131.log_bounds (by decide : 0<grid) PrefixTable131.state_50).1
    norm_num [Lower,Div,grid] at hn ⊢
    exact hn

theorem log_local {N L j : ℕ} (hL : 1≤L) (hhigh : N≤705097)
    (hj : j≤7) (hleft : (L : ℝ)<(N : ℝ)/Div j) : Real.log L ≤ LocalLog j := by
  have hLp : (0 : ℝ)<L := by exact_mod_cast (show 0<L by omega)
  have hd := div_pos j
  have hm : (L : ℝ)*Div j ≤ N := (le_div_iff₀ hd).mp hleft.le
  have hNp : 0<N := by
    have hh : (0 : ℝ)<N := (mul_pos hLp hd).trans_le hm
    exact_mod_cast hh
  have hh := Real.log_le_log (mul_pos hLp hd) hm
  rw [Real.log_mul hLp.ne' hd.ne'] at hh
  have ht := log_cap (by omega : 1≤N) hhigh
  have hb := lower_log hj
  dsimp only [LocalLog]
  linarith only [hh,ht,hb]

theorem local_payment {N L j : ℕ} (hL : 1≤L) (hhigh : N≤705097)
    (hj : j≤7) (hleft : (L : ℝ)<(N : ℝ)/Div j) :
    (102/25+2*Harmonic L+FrontierSum208.Polynomial (Real.log L))*(L : ℝ) ≤
      LocalCoeff j*L := by
  have hl := log_local hL hhigh hj hleft
  have hh := HarmonicAbel29.harmonic_le_one_add_log L
  have hp := ActualRecoveryChain208.polynomial_mono
    (Real.log_nonneg (by exact_mod_cast hL)) hl
  have h1 := mul_le_mul_of_nonneg_right hl (Nat.cast_nonneg (α := ℝ) L)
  have h2 := mul_le_mul_of_nonneg_right hh (Nat.cast_nonneg (α := ℝ) L)
  have h3 := mul_le_mul_of_nonneg_right hp (Nat.cast_nonneg (α := ℝ) L)
  dsimp only [LocalCoeff]
  nlinarith only [h1,h2,h3]
#print axioms state_99
#print axioms lower_log
#print axioms local_payment
end
end JSP233.RecoveryLocalization212
