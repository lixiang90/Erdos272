import Erdos272.Arithmetic.LightPhaseAnalytic209
import Erdos272.Arithmetic.LightPeriodic209

namespace JSP233.LightPhaseSum209
open LightPhaseAnalytic209 LightPeriodic209 PrefixAbel208
open scoped BigOperators
noncomputable section
set_option maxHeartbeats 0

def Phase (N d k r B V E : ℕ) : ℕ :=
  min d (N-k*d)*min V (N/d-r*B+E)

theorem phase_zero {N d k r B V E : ℕ} (hk : 0<k) (hd : N/k<d) :
    Phase N d k r B V E=0 := by
  have hh : N<d*k := (Nat.div_lt_iff_lt_mul hk).mp hd
  have hz : N-k*d=0 := by
    rw [Nat.mul_comm k d]
    exact Nat.sub_eq_zero_of_le hh.le
  simp [Phase,hz]

theorem phase_sum_cut (N k r B V E : ℕ) (hk : 0<k) (a : ℕ→ℝ) :
    (∑i∈Finset.range N,a i*(Phase N (i+1) k r B V E:ℝ))=
      ∑i∈Finset.range (N/k),a i*(Phase N (i+1) k r B V E:ℝ) := by
  symm
  apply Finset.sum_subset (Finset.range_mono (Nat.div_le_self N k))
  intro i hi hn
  have hni : N / k < i + 1 := Nat.lt_succ_of_le
    (by simpa only [Finset.mem_range,not_lt] using hn)
  rw [phase_zero hk hni,Nat.cast_zero,mul_zero]

theorem phase_real_cap {N d k r B V E : ℕ} (hd : 0<d) :
    (Phase N d k r B V E:ℝ)≤Cap N V E d := by
  have hh := LightPhaseAnalytic209.phase_le_cap (N:=N) (k:=k) (r:=r)
    (B:=B) (V:=V) (E:=E) hd
  unfold Phase Cap
  exact_mod_cast hh

theorem phase_weighted {N k r B V E : ℕ} (hk : 0<k) (hEV : E<V)
    (a : ℕ→ℝ) (rho lo hi : ℝ) (hrho : 0≤rho) (hlo : lo≤0) (hhi : 0≤hi)
    (ha : ∀i<N,0≤a i)
    (hprefix : ∀n,1≤n → n≤N →
      rho*n+lo≤Prefix a n ∧ Prefix a n≤rho*n+hi) :
    (∑i∈Finset.range N,a i*(Phase N (i+1) k r B V E:ℝ))≤
      rho*(N:ℝ)^2*Coeff V E k+(rho+hi-lo)*(V:ℝ)*N/k := by
  have hE : (0:ℝ)≤E := by positivity
  have hV : (0:ℝ)≤V := by positivity
  have hEVR : (E:ℝ)<V := by exact_mod_cast hEV
  have hkR : (0:ℝ)<k := by exact_mod_cast hk
  let q:=N/k
  have hq : q≤N := Nat.div_le_self N k
  have hqR : (q:ℝ)≤(N:ℝ)/k := by
    apply (le_div_iff₀ hkR).mpr
    exact_mod_cast Nat.div_mul_le_self N k
  have hw (i : ℕ) : 0≤Cap (N:ℝ) V E (i+1:ℕ) :=
    cap_nonneg (by positivity) hV hE (by positivity)
  have hinc : ∀i, i+1<q → Cap (N:ℝ) V E (i+1:ℕ)≤Cap N V E (i+2:ℕ) := by
    intro i hi'
    apply cap_mono hV hE
    exact_mod_cast Nat.le_add_right (i+1) 1
  have hab := weighted_increasing a (fun i => Cap (N:ℝ) V E (i+1:ℕ)) q rho lo hi hlo
    (fun n hn hnq => hprefix n hn (hnq.trans hq))
    (fun i hi' => hw i) (by simpa only [Nat.add_assoc] using hinc)
  have hpeak : (if q=0 then 0 else Cap (N:ℝ) V E (q-1+1:ℕ))≤(V:ℝ)*N/k := by
    split_ifs with hz
    · positivity
    · have he : q-1+1=q := Nat.sub_add_cancel (Nat.one_le_iff_ne_zero.mpr hz)
      rw [he]
      have h1 : Cap (N:ℝ) V E q≤(V:ℝ)*q := min_le_left _ _
      have h2 := mul_le_mul_of_nonneg_left hqR hV
      simpa only [mul_div_assoc] using h1.trans h2
  have hsum : (∑i∈Finset.range q,Cap (N:ℝ) V E (i+1:ℕ))=
      ∑d∈Finset.Icc 1 q,Cap (N:ℝ) V E d := by
    induction q with
    | zero => simp
    | succ q ih => rw [Finset.sum_range_succ,Finset.sum_Icc_succ_top (by omega),ih]
  rw [phase_sum_cut N k r B V E hk]
  calc
    _≤∑i∈Finset.range q,a i*Cap (N:ℝ) V E (i+1:ℕ) := by
      apply Finset.sum_le_sum
      intro i hi'
      exact mul_le_mul_of_nonneg_left (phase_real_cap (by omega))
        (ha i ((Finset.mem_range.mp hi').trans_le hq))
    _≤rho*(∑i∈Finset.range q,Cap (N:ℝ) V E (i+1:ℕ))+
        (hi-lo)*(if q=0 then 0 else Cap (N:ℝ) V E (q-1+1:ℕ)) := hab
    _≤rho*((N:ℝ)^2*Coeff V E k+(V:ℝ)*N/k)+(hi-lo)*((V:ℝ)*N/k) := by
      apply add_le_add
      · rw [hsum]
        exact mul_le_mul_of_nonneg_left (cap_sum_le (by positivity) hE hEVR hkR hqR) hrho
      · exact mul_le_mul_of_nonneg_left hpeak (by linarith only [hhi,hlo])
    _=_ := by ring

#print axioms phase_weighted
end
end JSP233.LightPhaseSum209
