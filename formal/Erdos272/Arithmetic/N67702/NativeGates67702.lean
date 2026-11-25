module

public import Erdos272.Counting.N86412.NativeDual86412
public import Erdos272.Retention.N67702.RecoveryCertificates67702
public import Erdos272.Retention.N86412.CoreSupply86412
public import Erdos272.Resources.N291012.RootModel291012

@[expose] public section

namespace JSP233.NativeGates67702
open Recovery208 NativeDual86412 LocalRecovery67702 RecoveryCertificates67702 RootModel291012
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2000000

def U : Fin 7→ℝ := ![809,138,41,2,1,1,0]
def V : Fin 7→ℝ := ![1193,93,19,192/1001,34/15,1,3]
def Slope : Fin 7→ℝ := ![192,16,4,192/1001,4/15,1,1]
def Constant : Fin 7→ℝ := ![6006,0,0,0,0,0,0]
def Centre (k : Fin 7) : ℝ :=
  Constant k+U k*LeftCentre (BLocal 0 18+1/2) (FineW 0)+V k*WidthCentre (BLocal 0 18+1/2) (FineW 0)

theorem native_gate (k : Fin 7) :
    0≤Slope k ∧ 0<Slope k*67702-Centre k ∧
    Dual (U k) (V k)*(FineA 0*67702+ShiftEnergy (BLocal 0 18+1/2) (FineW 0) FineC) <
      (Slope k*67702-Centre k)^2 ∧
    0≤2*Slope k*(Slope k*67702-Centre k)-Dual (U k) (V k)*FineA 0 := by
  fin_cases k <;>
    norm_num [U, V, Slope, Constant, Centre, Dual, LeftCentre, WidthCentre, ShiftEnergy,
      FineA, FineW, FineC, BLocal, HLocal, LogLocal,
      RecoveryParameters291012.Lower, CovarianceScalar213.Polynomial]

theorem actual_direction {n L w : ℝ} (hn : 67702≤n)
    (hp : WidthProfile L w ≤ FineA 0*n+(BLocal 0 18+1/2)*L+FineW 0*w+FineC) (k : Fin 7) :
    U k*L+V k*w+Constant k < Slope k*n := by
  have hc := native_gate k
  obtain ⟨ht, hg⟩ := continuous_square_gate hn hc.1 hc.2.1 hc.2.2.1 hc.2.2.2
  have he : Slope k*n-Centre k = (Slope k*n-Constant k)-
      (U k*LeftCentre (BLocal 0 18+1/2) (FineW 0)+V k*WidthCentre (BLocal 0 18+1/2) (FineW 0)) := by
    unfold Centre
    ring
  rw [he] at ht hg
  have h := actual_dual_bound hp ht hg
  linarith only [h]

theorem native_from_profile {N L R : ℕ} (hN : 67702≤N) (hRN : R≤N)
    (hwidth : 32*(L+N-R)≤3*N)
    (hp : WidthProfile L (Width N L R) ≤ FineA 0*N+(BLocal 0 18+1/2)*L+FineW 0*Width N L R+FineC) :
    CoreSupply86412.Native N L R := by
  let w := L+N-R
  have hw : (w : ℝ)=Width N L R := by
    dsimp only [w, Width]
    rw [Nat.cast_sub (by omega : R≤L+N)]
    push_cast
    ring
  have hn : (67702 : ℝ)≤N := by exact_mod_cast hN
  have h0 := actual_direction hn hp (0 : Fin 7)
  have h1 := actual_direction hn hp (1 : Fin 7)
  have h2 := actual_direction hn hp (2 : Fin 7)
  have h3 := actual_direction hn hp (3 : Fin 7)
  have h4 := actual_direction hn hp (4 : Fin 7)
  have h5 := actual_direction hn hp (5 : Fin 7)
  have h6 := actual_direction hn hp (6 : Fin 7)
  change (809 : ℝ)*L+1193*Width N L R+6006<192*N at h0
  change (138 : ℝ)*L+93*Width N L R+0<16*N at h1
  change (41 : ℝ)*L+19*Width N L R+0<4*N at h2
  change (2 : ℝ)*L+(192/1001)*Width N L R+0<(192/1001)*N at h3
  change (1 : ℝ)*L+(34/15)*Width N L R+0<(4/15)*N at h4
  change (1 : ℝ)*L+1*Width N L R+0<1*N at h5
  change (0 : ℝ)*L+3*Width N L R+0<1*N at h6
  norm_num only [zero_mul, one_mul, add_zero, zero_add] at h0 h1 h2 h3 h4 h5 h6
  rw [←hw] at h0 h1 h2 h3 h4 h5 h6
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, hwidth⟩
  · exact_mod_cast h0
  · exact_mod_cast h1.le
  · exact_mod_cast h2.le
  · have h : (1001 : ℝ)*L+96*(w : ℝ)≤96*N := by nlinarith only [h3]
    exact_mod_cast h
  · have h : (15 : ℝ)*L+34*(w : ℝ)≤4*N := by nlinarith only [h4]
    exact_mod_cast h
  · exact_mod_cast h5.le
  · exact_mod_cast h6.le

#print axioms native_gate
#print axioms actual_direction
#print axioms native_from_profile
end
end JSP233.NativeGates67702
