module

public import Erdos272.Arithmetic.PrefixState131
public import Erdos272.Arithmetic.EndpointLog131

@[expose] public section
namespace JSP233.PrefixLog131
open PrefixState131
noncomputable section
set_option maxHeartbeats 0

theorem log_bounds {G n : ℕ} {s : State} (hG : 0<G) (hv : Valid G n s) :
    (s.logLo:ℝ)/(G:ℝ)≤Real.log n ∧ Real.log n≤(s.logHi:ℝ)/(G:ℝ) := by
  have hGp : (0:ℝ)<G := Nat.cast_pos.mpr hG
  exact ⟨(div_le_iff₀ hGp).mpr (by simpa only [mul_comm] using hv.1),
    (le_div_iff₀ hGp).mpr (by simpa only [mul_comm] using hv.2.1)⟩

theorem log_square_bounds {G r : ℕ} {s : State} (hG : 0<G) (hv : Valid G r s) :
    2*((s.logLo:ℝ)/(G:ℝ))≤Real.log ((r^2:ℕ):ℝ) ∧
      Real.log ((r^2:ℕ):ℝ)≤2*((s.logHi:ℝ)/(G:ℝ)) := by
  have hh := log_bounds hG hv
  rw [Nat.cast_pow,Real.log_pow]
  norm_num only [Nat.cast_ofNat]
  constructor <;> linarith only [hh.1,hh.2]

theorem log_endpoint_upper {G m N u : ℕ} {s : State}
    (hG : 0<G) (hv : Valid G m s) (hm : 0<m) (hN : 0<N) (hu : N≤u) :
    Real.log (N:ℝ)≤2*((s.logHi:ℝ)/(G:ℝ))+
      ((u:ℝ)-(m:ℝ)^2)/(m:ℝ)^2 := by
  have hu0 : (0:ℝ)<u := Nat.cast_pos.mpr (lt_of_lt_of_le hN hu)
  exact (Real.log_le_log (Nat.cast_pos.mpr hN) (by exact_mod_cast hu)).trans
    (EndpointLog131.log_upper_from_square hu0 hm (log_bounds hG hv).2)

#print axioms log_bounds
#print axioms log_square_bounds
#print axioms log_endpoint_upper
end
end JSP233.PrefixLog131
