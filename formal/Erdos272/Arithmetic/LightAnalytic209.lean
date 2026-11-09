module

public import Erdos272.Arithmetic.LightPhaseSum209
public import Erdos272.Arithmetic.LightSeries209
public import Mathlib.Algebra.BigOperators.Ring.Finset

@[expose] public section

namespace JSP233.LightAnalytic209
open LightPhaseAnalytic209 LightPhaseSum209 LightSeries209 PrefixAbel208
open LightClosed208
open scoped BigOperators
noncomputable section
set_option maxHeartbeats 0

def Alpha (A B V E : ℝ) (L : ℕ) : ℝ :=
  (∑r∈Finset.range L,Coeff V E (A+(r:ℝ)*B))+V/(2*B*(A+(L-1:ℕ)*B))

def LogFactor (A B HIGH : ℝ) : ℝ := 1/A+Real.log (HIGH/A)/B

/-- A periodic discrepancy certificate pays the actual O(1) light price.
The cutoff L is arbitrary; all physical phases are covered. -/
theorem weighted_closed {N T E B V HIGH L : ℕ} (hET : E<T) (hTV : T≤V)
    (hB : 0<B) (hNH : N≤HIGH) (hAH : T-E≤HIGH) (hL : 1≤L)
    (a : ℕ→ℝ) (rho lo hi : ℝ) (hrho : 0≤rho) (hlo : lo≤0) (hhi : 0≤hi)
    (ha : ∀i<N,0≤a i)
    (hprefix : ∀n,1≤n → n≤N →
      rho*n+lo≤Prefix a n ∧ Prefix a n≤rho*n+hi) :
    (∑i∈Finset.range N,a i*(LightPrice208.Closed N (i+1) T E B V:ℝ))≤
      rho*Alpha (T-E:ℕ) B V E L*(N:ℝ)^2+
        ((rho+hi-lo)*(V:ℝ)*LogFactor (T-E:ℕ) B HIGH)*N := by
  let A:=T-E
  let m:=Count N A B
  have hA : 0<A := Nat.sub_pos_of_lt hET
  have hAR : (0:ℝ)<A := by exact_mod_cast hA
  have hBR : (0:ℝ)<B := by exact_mod_cast hB
  have hEV : E<V := hET.trans_le hTV
  have hEVR : (E:ℝ)<V := by exact_mod_cast hEV
  have hK (r : ℕ) : 0<A+r*B := by omega
  have hm : m≤N+1 := by
    simpa only [Nat.div_one] using (LightPrice208.count_le_ground (N:=N) (d:=1) (A:=A) hB)
  have hprices : (∑i∈Finset.range N,a i*(LightPrice208.Closed N (i+1) T E B V:ℝ))=
      ∑r∈Finset.range m,∑i∈Finset.range N,a i*(Phase N (i+1) (A+r*B) r B V E:ℝ) := by
    calc
      _=∑i∈Finset.range N,∑r∈Finset.range (N+1),
          a i*(Phase N (i+1) (A+r*B) r B V E:ℝ) := by
        apply Finset.sum_congr rfl
        intro i hi'
        rw [←LightPrice208.price_closed (by omega : 0 < i + 1) hB hET.le hTV]
        simp only [LightPhases208.Price,Nat.cast_sum,Finset.mul_sum]
        rfl
      _=∑r∈Finset.range (N+1),∑i∈Finset.range N,
          a i*(Phase N (i+1) (A+r*B) r B V E:ℝ) := Finset.sum_comm
      _=_ := by
        symm
        apply Finset.sum_subset (Finset.range_mono hm)
        intro r hr hn
        have hmr : m≤r := by simpa only [Finset.mem_range,not_lt] using hn
        have hgt : N<A+r*B := by
          by_contra! hn'
          have hh : r<m := (lt_count hB).mpr hn'
          omega
        apply Finset.sum_eq_zero
        intro i hi'
        have hz : N-(A+r*B)*(i+1)=0 := by
          have hp := Nat.le_mul_of_pos_right (A+r*B) (by omega : 0 < i + 1)
          omega
        simp only [Phase,hz,min_zero,zero_mul,Nat.cast_zero,mul_zero]
  have hphase : (∑r∈Finset.range m,∑i∈Finset.range N,
      a i*(Phase N (i+1) (A+r*B) r B V E:ℝ))≤
      ∑r∈Finset.range m,
        (rho*(N:ℝ)^2*Coeff V E (A+(r:ℝ)*B)+(rho+hi-lo)*(V:ℝ)*N/(A+(r:ℝ)*B)) := by
    apply Finset.sum_le_sum
    intro r hr
    simpa only [Nat.cast_add,Nat.cast_mul] using
      phase_weighted (hK r) hEV a rho lo hi hrho hlo hhi ha hprefix
  have hc := coeff_prefix_tail hAR hBR (by positivity : (0:ℝ)≤E) hEVR L m hL
  have hh := reciprocal_prefix hAR hBR (show (A:ℝ)≤HIGH by exact_mod_cast hAH) m
    (fun r hr => by
      have hkN : A+r*B≤N := (lt_count hB).mp hr
      have hhN : A+r*B≤HIGH := hkN.trans hNH
      exact_mod_cast hhN)
  have hsum : (∑r∈Finset.range m,
      (rho*(N:ℝ)^2*Coeff V E (A+(r:ℝ)*B)+(rho+hi-lo)*(V:ℝ)*N/(A+(r:ℝ)*B)))=
      (rho*(N:ℝ)^2)*(∑r∈Finset.range m,Coeff V E (A+(r:ℝ)*B))+
        ((rho+hi-lo)*(V:ℝ)*N)*(∑r∈Finset.range m,1/(A+(r:ℝ)*B)) := by
    simp only [Finset.sum_add_distrib,Finset.mul_sum]
    congr 1
    apply Finset.sum_congr rfl
    intro r hr
    ring
  rw [hprices]
  calc
    _≤_ := hphase
    _=_ := hsum
    _≤(rho*(N:ℝ)^2)*Alpha A B V E L+
        ((rho+hi-lo)*(V:ℝ)*N)*LogFactor A B HIGH := by
      exact add_le_add (mul_le_mul_of_nonneg_left hc (by positivity))
        (mul_le_mul_of_nonneg_left hh (by
          have hz : 0≤rho+hi-lo := by linarith
          exact mul_nonneg (mul_nonneg hz (Nat.cast_nonneg V)) (Nat.cast_nonneg N)))
    _=_ := by unfold A; ring

#print axioms weighted_closed
end
end JSP233.LightAnalytic209
