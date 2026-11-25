module

public import Erdos272.Retention.N153080.RecoveryCertificates153080

@[expose] public section

namespace JSP233.DualRecovery153080
open Recovery208 LocalRecovery158375 RecoveryCertificates153080
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1000000

def Dual : ℝ := 921007748591/3359

def NativeCentre : ℝ :=
  2811*LeftCentre (BLocal 18) FineW+1193*WidthCentre (BLocal 18) FineW

theorem dual_square_bound (x y : ℝ) :
    (2811*x+1193*y)^2 ≤ Dual*WidthProfile x y := by
  have hid : Dual*WidthProfile x y-(2811*x+1193*y)^2 =
      (322109887*x-190939400*y)^2/268720000 := by
    dsimp only [Dual, WidthProfile]
    ring
  have hn : (0 : ℝ) ≤ (322109887*x-190939400*y)^2/268720000 :=
    div_nonneg (sq_nonneg _) (by norm_num)
  linarith only [hid, hn]

theorem actual_dual_bound {n L w A tL tw C target : ℝ}
    (hp : WidthProfile L w ≤ A*n+tL*L+tw*w+C)
    (ht : 0 < target-(2811*LeftCentre tL tw+1193*WidthCentre tL tw))
    (hg : Dual*(A*n+ShiftEnergy tL tw C) <
      (target-(2811*LeftCentre tL tw+1193*WidthCentre tL tw))^2) :
    2811*L+1193*w < target := by
  have hs := actual_profile_shift hp
  have hb := dual_square_bound (L-LeftCentre tL tw) (w-WidthCentre tL tw)
  have hpaid := mul_le_mul_of_nonneg_left hs (show (0 : ℝ) ≤ Dual by norm_num [Dual])
  have hsq : (2811*L+1193*w-(2811*LeftCentre tL tw+1193*WidthCentre tL tw))^2 ≤
      Dual*(A*n+ShiftEnergy tL tw C) := by
    calc
      _ = (2811*(L-LeftCentre tL tw)+1193*(w-WidthCentre tL tw))^2 := by ring
      _ ≤ _ := hb.trans hpaid
  by_contra hh
  have hge : target ≤ 2811*L+1193*w := le_of_not_gt hh
  have hprod := mul_nonneg (sub_nonneg.mpr hge)
    (show 0 ≤ 2811*L+1193*w+target-2*(2811*LeftCentre tL tw+1193*WidthCentre tL tw)
      by linarith only [ht, hge])
  nlinarith only [hsq, hg, hprod]

theorem native_gate :
    0 < 192*151879-NativeCentre ∧
    Dual*(FineA*151879+ShiftEnergy (BLocal 18) FineW FineC) <
      (192*151879-NativeCentre)^2 ∧
    0 ≤ 2*192*(192*151879-NativeCentre)-Dual*FineA := by
  norm_num [NativeCentre, Dual, LeftCentre, WidthCentre, ShiftEnergy,
    FineA, FineW, FineC, BLocal, HLocal, LogLocal,
    RecoveryParameters291012.Lower, CovarianceScalar213.Polynomial]

theorem actual_native_thin {n L w : ℝ} (hn : 151879 ≤ n)
    (hp : WidthProfile L w ≤ FineA*n+BLocal 18*L+FineW*w+FineC) :
    2811*L+1193*w < 192*n := by
  obtain ⟨ht, hg⟩ := continuous_square_gate hn (by norm_num : (0 : ℝ) ≤ 192)
    native_gate.1 native_gate.2.1 native_gate.2.2
  exact actual_dual_bound hp ht hg

#print axioms dual_square_bound
#print axioms actual_dual_bound
#print axioms native_gate
#print axioms actual_native_thin
end
end JSP233.DualRecovery153080
