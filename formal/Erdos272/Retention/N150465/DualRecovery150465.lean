module

public import Erdos272.Retention.N150465.RecoveryCertificates150465
public import Erdos272.Retention.N153080.DualRecovery153080

@[expose] public section

namespace JSP233.DualRecovery150465
open Recovery208 LocalRecovery150465 RecoveryCertificates150465
open DualRecovery153080 (Dual)
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1000000

def NativeCentre : ℝ :=
  2811*LeftCentre (BLocal 18) FineW+1193*WidthCentre (BLocal 18) FineW

theorem native_gate :
    0 < 192*150000-NativeCentre ∧
    Dual*(FineA*150000+ShiftEnergy (BLocal 18) FineW FineC) <
      (192*150000-NativeCentre)^2 ∧
    0 ≤ 2*192*(192*150000-NativeCentre)-Dual*FineA := by
  norm_num [NativeCentre, Dual, LeftCentre, WidthCentre, ShiftEnergy,
    FineA, FineW, FineC, BLocal, HLocal, LogLocal,
    RecoveryParameters291012.Lower, CovarianceScalar213.Polynomial]

theorem actual_native_thin {n L w : ℝ} (hn : 150000 ≤ n)
    (hp : WidthProfile L w ≤ FineA*n+BLocal 18*L+FineW*w+FineC) :
    2811*L+1193*w < 192*n := by
  obtain ⟨ht, hg⟩ := continuous_square_gate hn (by norm_num : (0 : ℝ) ≤ 192)
    native_gate.1 native_gate.2.1 native_gate.2.2
  exact DualRecovery153080.actual_dual_bound hp ht hg

#print axioms native_gate
#print axioms actual_native_thin
end
end JSP233.DualRecovery150465
