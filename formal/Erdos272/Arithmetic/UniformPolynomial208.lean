import Erdos272.Arithmetic.UniformLow208

/-! Closed step polynomials and their exact cubic differences. -/
namespace JSP233.UniformPolynomial208
open UniformSourceCore208 UniformLow208
noncomputable section
set_option maxHeartbeats 0

def JP (D : ℕ) (y z : ℝ) : ℝ :=
  y^3/6-Delta*((D : ℝ)*y*(y-z)^2/2-(D : ℝ)*((D : ℝ)+1)*(y-z)^3/6+
    y^3/6*(UniformSourceCore208.Sigma-H2 D))+
    Delta/2*((D : ℝ)*y*(y-z)-(D : ℝ)*((D : ℝ)+1)*(y-z)^2/2)-11*y^2/80-2014*y/625

def JD (D : ℕ) (y z : ℝ) : ℝ :=
  (1-Delta*UniformSourceCore208.Sigma+Delta*(H2 D-1))*y^2/2+
    Delta*(y-(D : ℝ)*(y-z))^2/2+Delta*(D : ℝ)*(y-(D : ℝ)*(y-z))/2-
      11*y/40-2014/625

theorem Jstar_eq_JP (y z : ℝ) : Jstar y z=JP (Step y (y-z)) y z := by
  unfold Jstar JP I w
  ring

theorem JP_simpson (D : ℕ) (a b z : ℝ) :
    JP D b z-JP D a z=(b-a)/6*(JD D a z+4*JD D ((a+b)/2) z+JD D b z) := by
  unfold JP JD
  ring

theorem H2_two_le {D : ℕ} (hD : 2≤D) : (5/4 : ℝ)≤H2 D := by
  have hsub : Finset.Icc 1 (2 : ℕ)⊆Finset.Icc 1 D := by
    intro d hd
    simp only [Finset.mem_Icc] at hd ⊢
    omega
  have hh : H2 2≤H2 D := Finset.sum_le_sum_of_subset_of_nonneg hsub
    (fun d hd hnot => by positivity)
  have htwo : H2 2=(5/4 : ℝ) := by norm_num [H2,Finset.sum_Icc_succ_top]
  rw [htwo] at hh
  exact hh

theorem JD_pos {D : ℕ} {y z : ℝ} (hD : 2≤D) (hy : 31≤y)
    (hcell : (D : ℝ)*(y-z)≤y) : 0<JD D y z := by
  have hH := H2_two_le hD
  have htheta : 0≤y-(D : ℝ)*(y-z) := by linarith only [hcell]
  have h1 := mul_nonneg (by norm_num [Delta] : (0 : ℝ)≤Delta/2)
    (sq_nonneg (y-(D : ℝ)*(y-z)))
  have hDelta : 0≤Delta := by norm_num [Delta]
  have h2 : 0≤Delta*(D : ℝ)*(y-(D : ℝ)*(y-z))/2 := by positivity
  have h3 := mul_nonneg (by norm_num [Delta] : (0 : ℝ)≤Delta)
    (by linarith only [hH] : 0≤H2 D-5/4)
  have h4 := mul_nonneg h3 (sq_nonneg y)
  have hyy := mul_nonneg (by linarith only [hy] : 0≤y-31) (by linarith only [hy] : 0≤y+31)
  unfold JD Delta UniformSourceCore208.Sigma at *
  nlinarith only [h1,h2,h4,hyy,hy]

theorem JP_mono_cell {D : ℕ} {a b z : ℝ} (hD : 2≤D) (ha : 31≤a) (hab : a≤b)
    (hca : (D : ℝ)*(a-z)≤a) (hcb : (D : ℝ)*(b-z)≤b) : JP D a z≤JP D b z := by
  have hja := JD_pos hD ha hca
  have hjb := JD_pos hD (ha.trans hab) hcb
  have hjm := JD_pos hD (by linarith only [ha,hab] : 31≤(a+b)/2)
    (by nlinarith only [hca,hcb] : (D : ℝ)*((a+b)/2-z)≤(a+b)/2)
  have hh := mul_nonneg (by linarith only [hab] : 0≤(b-a)/6)
    (by linarith only [hja,hjb,hjm] : 0≤JD D a z+4*JD D ((a+b)/2) z+JD D b z)
  rw [← JP_simpson] at hh
  linarith only [hh]

theorem JP_boundary (D : ℕ) (hD : 1≤D) (z : ℝ) :
    JP (D+1) (((D : ℝ)+1)*z/(D : ℝ)) z=JP D (((D : ℝ)+1)*z/(D : ℝ)) z := by
  have hD0 : (D : ℝ)≠0 := by positivity
  have hD1 : (D : ℝ)+1≠0 := by positivity
  unfold JP H2
  rw [Finset.sum_Icc_succ_top (by omega : 1≤D+1)]
  push_cast
  field_simp
  ring

#print axioms JD_pos
#print axioms JP_mono_cell
#print axioms JP_boundary
end
end JSP233.UniformPolynomial208
