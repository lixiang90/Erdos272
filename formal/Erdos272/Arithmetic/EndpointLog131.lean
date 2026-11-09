module

public import Erdos272.Arithmetic.LogIncrement131

@[expose] public section
namespace JSP233.EndpointLog131
set_option maxHeartbeats 0
noncomputable section

theorem log_upper_from_square {u c:ℝ} {m:ℕ} (hu:0<u) (hm:0<m)
    (hc:Real.log (m:ℝ)≤c) :
    Real.log u≤2*c+(u-(m:ℝ)^2)/(m:ℝ)^2 := by
  have hmR : (0:ℝ)<m := by exact_mod_cast hm
  have hsq : (0:ℝ)<(m:ℝ)^2 := sq_pos_of_pos hmR
  have h := Real.log_le_sub_one_of_pos (div_pos hu hsq)
  rw [Real.log_div hu.ne' hsq.ne',Real.log_pow] at h
  norm_num only [Nat.cast_ofNat] at h
  have he : u/(m:ℝ)^2-1=(u-(m:ℝ)^2)/(m:ℝ)^2 := by
    field_simp
  rw [he] at h
  linarith only [h,hc]

#print axioms log_upper_from_square
end
end JSP233.EndpointLog131
