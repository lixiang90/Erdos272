module

public import Mathlib.Analysis.Complex.ExponentialBounds
public import Mathlib.Data.Nat.Factorial.Basic

@[expose] public section
namespace JSP233.LogIncrement131
open scoped BigOperators
set_option maxHeartbeats 0
set_option maxRecDepth 200000

def C32 : ℕ := Nat.factorial 32
def num32 (n:ℕ) : ℕ := (n-1)*∑i∈Finset.range 32,(C32/(i+1))*n^(31-i)
def den32 (n:ℕ) : ℕ := C32*n^32*(n-1)
def a4 (n:ℕ) : ℕ := 12*n^3+6*n^2+4*n+3
def num4 (n:ℕ) : ℕ := a4 n*(n-1)
def den4 (n:ℕ) : ℕ := 12*n^4*(n-1)
def stepCheck (G n lo hi:ℕ) : Bool :=
  if n≤32 then
    decide (lo*den32 n+G*C32≤G*num32 n) && decide (G*num32 n+G*C32≤hi*den32 n)
  else
    decide (lo*den4 n+12*G≤G*num4 n) && decide (G*num4 n+12*G≤hi*den4 n)

noncomputable section
open scoped Classical

def S (n k:ℕ) : ℝ := ∑i∈Finset.range k,(1/(n:ℝ))^(i+1)/(i+1)
def R (n k:ℕ) : ℝ := 1/((n:ℝ)^k*((n:ℝ)-1))

theorem log_increment_error {n:ℕ} (hn:2≤n) (k:ℕ) :
    |Real.log (n:ℝ)-Real.log ((n-1:ℕ):ℝ)-S n k|≤R n k := by
  have hn1 : 1≤n := by omega
  have hnR : (1:ℝ)<n := by exact_mod_cast hn
  have hn0 : (0:ℝ)<n := by linarith only [hnR]
  have hnm : (0:ℝ)<(n:ℝ)-1 := by linarith only [hnR]
  have hnmNat : (0:ℝ)<((n-1:ℕ):ℝ) := by exact_mod_cast (show 0<n-1 by omega)
  have habs : |(1:ℝ)/(n:ℝ)|<1 := by
    rw [abs_of_nonneg (by positivity)]
    exact (div_lt_one hn0).mpr hnR
  have h := Real.abs_log_sub_add_sum_range_le (x:=1/(n:ℝ)) habs k
  rw [abs_of_nonneg (by positivity : (0:ℝ)≤1/(n:ℝ))] at h
  have he : (1:ℝ)-1/(n:ℝ)=((n-1:ℕ):ℝ)/(n:ℝ) := by
    rw [Nat.cast_sub hn1]
    norm_num only [Nat.cast_one]
    field_simp
  rw [he,Real.log_div hnmNat.ne' hn0.ne'] at h
  change |S n k+(Real.log ((n-1:ℕ):ℝ)-Real.log (n:ℝ))|≤_ at h
  rw [←he] at h
  have hneg : S n k+(Real.log ((n-1:ℕ):ℝ)-Real.log (n:ℝ))=
      -(Real.log (n:ℝ)-Real.log ((n-1:ℕ):ℝ)-S n k) := by ring
  rw [hneg,abs_neg] at h
  have herr : ((1:ℝ)/(n:ℝ))^(k+1)/(1-1/(n:ℝ))=R n k := by
    dsimp only [R]
    simp only [one_div,inv_pow,pow_succ]
    field_simp
  rwa [herr] at h

theorem log_increment_bounds {n:ℕ} (hn:2≤n) (k:ℕ) :
    S n k-R n k≤Real.log (n:ℝ)-Real.log ((n-1:ℕ):ℝ) ∧
      Real.log (n:ℝ)-Real.log ((n-1:ℕ):ℝ)≤S n k+R n k := by
  have h := abs_le.mp (log_increment_error hn k)
  constructor <;> linarith only [h.1,h.2]

theorem s4_fraction {n:ℕ} (hn:2≤n) : S n 4=(num4 n:ℝ)/(den4 n:ℝ) := by
  have hn1 : 1≤n := by omega
  have hn0 : (n:ℝ)≠0 := by exact_mod_cast (show n≠0 by omega)
  have hnR : (1:ℝ)<n := by exact_mod_cast hn
  have hnm : (n:ℝ)-1≠0 := by linarith only [hnR]
  norm_num [S,num4,den4,a4,Finset.sum_range_succ,Nat.cast_sub hn1]
  field_simp
  ring

theorem r4_fraction {n:ℕ} (hn:2≤n) : R n 4=(12:ℝ)/(den4 n:ℝ) := by
  have hn1 : 1≤n := by omega
  have hn0 : (n:ℝ)≠0 := by exact_mod_cast (show n≠0 by omega)
  have hnR : (1:ℝ)<n := by exact_mod_cast hn
  have hnm : (n:ℝ)-1≠0 := by linarith only [hnR]
  dsimp only [R,den4]
  push_cast
  rw [Nat.cast_sub hn1]
  norm_num only [Nat.cast_one]
  field_simp

theorem s32_fraction {n:ℕ} (hn:2≤n) : S n 32=(num32 n:ℝ)/(den32 n:ℝ) := by
  have hn1 : 1≤n := by omega
  have hn0 : (n:ℝ)≠0 := by exact_mod_cast (show n≠0 by omega)
  have hnR : (1:ℝ)<n := by exact_mod_cast hn
  have hnm : (n:ℝ)-1≠0 := by linarith only [hnR]
  norm_num [S,num32,den32,C32,Finset.sum_range_succ,Nat.cast_sub hn1,Nat.factorial]
  field_simp
  ring

theorem r32_fraction {n:ℕ} (hn:2≤n) : R n 32=(C32:ℝ)/(den32 n:ℝ) := by
  have hn1 : 1≤n := by omega
  have hn0 : (n:ℝ)≠0 := by exact_mod_cast (show n≠0 by omega)
  have hnR : (1:ℝ)<n := by exact_mod_cast hn
  have hnm : (n:ℝ)-1≠0 := by linarith only [hnR]
  norm_num [R,den32,C32,Nat.cast_sub hn1,Nat.factorial]
  field_simp

theorem ratio_certificate_sound {G D A E lo hi:ℕ} (hG:0<G) (hD:0<D)
    (hl:lo*D+G*E≤G*A) (hu:G*A+G*E≤hi*D) :
    (lo:ℝ)/(G:ℝ)≤(A:ℝ)/(D:ℝ)-(E:ℝ)/(D:ℝ) ∧
      (A:ℝ)/(D:ℝ)+(E:ℝ)/(D:ℝ)≤(hi:ℝ)/(G:ℝ) := by
  have hGR : (0:ℝ)<G := by exact_mod_cast hG
  have hDR : (0:ℝ)<D := by exact_mod_cast hD
  have hlR : (lo:ℝ)*D+G*E≤G*A := by exact_mod_cast hl
  have huR : (G:ℝ)*A+G*E≤hi*D := by exact_mod_cast hu
  rw [←sub_div,←add_div]
  constructor
  · apply (div_le_div_iff₀ hGR hDR).mpr
    nlinarith only [hlR]
  · apply (div_le_div_iff₀ hDR hGR).mpr
    nlinarith only [huR]

theorem log_step_cert_sound {G n lo hi:ℕ} (hn:2≤n) (hG:0<G)
    (h:stepCheck G n lo hi=true) :
    (lo:ℝ)/(G:ℝ)≤Real.log (n:ℝ)-Real.log ((n-1:ℕ):ℝ) ∧
      Real.log (n:ℝ)-Real.log ((n-1:ℕ):ℝ)≤(hi:ℝ)/(G:ℝ) := by
  have hn0 : 0<n := by omega
  have hnm : 0<n-1 := by omega
  by_cases hsmall:n≤32
  · simp only [stepCheck,if_pos hsmall,Bool.and_eq_true,decide_eq_true_eq] at h
    have hd : 0<den32 n := by dsimp only [den32,C32];positivity
    have hp := ratio_certificate_sound hG hd h.1 h.2
    have ht := log_increment_bounds hn 32
    rw [s32_fraction hn,r32_fraction hn] at ht
    exact ⟨hp.1.trans ht.1,ht.2.trans hp.2⟩
  · simp only [stepCheck,if_neg hsmall,Bool.and_eq_true,decide_eq_true_eq] at h
    have hd : 0<den4 n := by dsimp only [den4];positivity
    have hp := ratio_certificate_sound (E:=12) hG hd
      (by simpa only [Nat.mul_comm] using h.1)
      (by simpa only [Nat.mul_comm] using h.2)
    have ht := log_increment_bounds hn 4
    rw [s4_fraction hn,r4_fraction hn] at ht
    exact ⟨hp.1.trans ht.1,ht.2.trans hp.2⟩

#print axioms log_increment_error
#print axioms log_increment_bounds
#print axioms s4_fraction
#print axioms r4_fraction
#print axioms s32_fraction
#print axioms r32_fraction
#print axioms ratio_certificate_sound
#print axioms log_step_cert_sound
end
end JSP233.LogIncrement131
