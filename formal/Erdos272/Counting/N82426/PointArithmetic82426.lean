module

public import Erdos272.Counting.N82427.DenseCount82427
public import Erdos272.Retention.N82427.RecoveryCertificates82427
public import Erdos272.Counting.N82427.JointDensity82427
public import Erdos272.Arithmetic.N82427.NativeGates82427

@[expose] public section

namespace JSP233.PointArithmetic82426
open StarCompletion APGeometry DenseDeletion40 IntrinsicTriples208 HarmonicAbel29
open RootModel291012 WitnessInterval43 Recovery208 RecoveryCaps213
open LocalRecovery82427 RecoveryCertificates82427 DensePool82427
open scoped Classical BigOperators
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2000000

theorem actual_count {E : Finset (Finset ℤ)} {rho beta : ℝ}
    (hE : Legal (Ground 82426) E) (hbad : ∀ S∈E, ¬IsAP S)
    (hdense : ∀ S∈E, rho*82426<S.card) (hrho : 1/12≤rho)
    (hgate : (82426 : ℝ)^3/6<beta*82426*Price (rho*82426)) :
    (E.card : ℝ)≤beta*82426 := by
  have hsize : (128 : ℝ)≤rho*82426 := by linarith only [hrho]
  have htheta := price_pos hsize
  have hpoint : ∀ S∈E, Price (rho*82426)≤((Pool S).card : ℝ) := by
    intro S hS
    have hd := hdense S hS
    have hs : 128≤S.card := by
      exact_mod_cast (show (128 : ℝ)≤S.card by linarith only [hsize, hd])
    exact (price_mono hsize hd.le).trans
      (actual_pool_price hs (by decide : 82426≤2^18) (hE.1 S hS) (hbad S hS))
  have hmass : Price (rho*82426)*(E.card : ℝ)≤∑ S∈E, ((Pool S).card : ℝ) := by
    calc
      _ = ∑ _S∈E, Price (rho*82426) := by simp [mul_comm]
      _ ≤ _ := Finset.sum_le_sum hpoint
  have hcapacity := actual_capacity hE
  rw [ground_card] at hcapacity
  have hpool : (∑ S∈E, ((Pool S).card : ℝ))≤(82426 : ℝ)^3/6 := by
    have hc : (∑ S∈E, ((Pool S).card : ℝ))≤((82426 : ℕ).choose 3 : ℝ) := by
      exact_mod_cast hcapacity
    rw [APResidual208.cast_choose_three] at hc
    nlinarith only [hc]
  by_contra hnot
  have hm := mul_lt_mul_of_pos_left (lt_of_not_ge hnot) htheta
  nlinarith only [hm, hmass, hpool, hgate]

theorem actual_deleted_count {F : Finset (Finset ℤ)} (hF : Legal (Ground 82426) F) :
    ((Deleted 82426 12 F).card : ℝ)≤(1609/20 : ℝ)*82426 := by
  apply actual_count (rho := 1/12) (beta := 1609/20) (actual_deleted_legal (r := 12) hF)
    (fun S hS => (Finset.mem_filter.mp hS).2.1)
  · intro S hS
    have hd : (82426 : ℝ)<12*(S.card : ℝ) := by
      exact_mod_cast (Finset.mem_filter.mp hS).2.2
    nlinarith only [hd]
  · norm_num
  · norm_num [Price]

theorem actual_omitted_count {c : ℕ} {F : Finset (Finset ℤ)}
    (hF : Legal (Ground 82426) F) :
    ((Omitted 82426 c F).card : ℝ)≤(1609/20 : ℝ)*82426 := by
  have hs : Omitted 82426 c F⊆Deleted 82426 12 F := Finset.filter_subset _ _
  have hc : ((Omitted 82426 c F).card : ℝ)≤(Deleted 82426 12 F).card := by
    exact_mod_cast Finset.card_le_card hs
  exact hc.trans (actual_deleted_count hF)

theorem actual_quarter_count {E : Finset (Finset ℤ)} (hE : Legal (Ground 82426) E)
    (hbad : ∀ S∈E, ¬IsAP S) (hdense : ∀ S∈E, (1/4 : ℝ)*82426<S.card) :
    (E.card : ℝ)≤(223/25 : ℝ)*82426 := by
  exact actual_count hE hbad hdense (by norm_num) (by norm_num [Price])

theorem actual_three_tenths_count {E : Finset (Finset ℤ)} (hE : Legal (Ground 82426) E)
    (hbad : ∀ S∈E, ¬IsAP S) (hdense : ∀ S∈E, (3/10 : ℝ)*82426<S.card) :
    (E.card : ℝ)≤(1239/200 : ℝ)*82426 := by
  exact actual_count hE hbad hdense (by norm_num) (by norm_num [Price])

theorem global_seventh :
    StageCertificate 82426 (CoarseA 0) (BGlobal 0) (HLocal 0) 872 (1/7) 1 := by
  norm_num [StageCertificate, LeftCentre, WidthCentre, ShiftEnergy, CoarseA,
    BGlobal, HLocal, LogLocal, CovarianceScalar213.Polynomial]

theorem coarse_local :
    StageCertificate 82426 (CoarseA 0) (BLocal 0 7) (HLocal 0) 872 (1/8) 1 := by
  norm_num [StageCertificate, LeftCentre, WidthCentre, ShiftEnergy, CoarseA,
    BLocal, HLocal, LogLocal, RecoveryParameters291012.Lower, CovarianceScalar213.Polynomial]

theorem quarter_stage :
    StageCertificate 82426 (QuarterA 0) (BLocal 0 8) (HLocal 0) 872 (17/250) (14/125) := by
  norm_num [StageCertificate, LeftCentre, WidthCentre, ShiftEnergy, QuarterA,
    BLocal, HLocal, LogLocal, RecoveryParameters291012.Lower, CovarianceScalar213.Polynomial]

theorem strong_stage :
    StageCertificate 82426 (StrongA 0) (BLocal 0 14) (HLocal 0) 872 (1/16) (11/100) := by
  norm_num [StageCertificate, LeftCentre, WidthCentre, ShiftEnergy, StrongA,
    BLocal, HLocal, LogLocal, RecoveryParameters291012.Lower, CovarianceScalar213.Polynomial]

theorem fine_final :
    StageCertificate 82426 (FineA 0) (BLocal 0 16) (FineW 0) FineC (1/18) (3/32) := by
  norm_num [StageCertificate, LeftCentre, WidthCentre, ShiftEnergy, FineA, FineW, FineC,
    BLocal, HLocal, LogLocal, RecoveryParameters291012.Lower, CovarianceScalar213.Polynomial]

theorem joint_certificate (i : Fin 2) :
    JointEllipse82427.Certificate (JointDensity82427.parameters i) (HLocal 0) 82426 := by
  fin_cases i <;>
    norm_num [JointEllipse82427.Certificate, JointEllipse82427.U, JointEllipse82427.V,
      JointEllipse82427.Z, JointEllipse82427.Determinant, JointEllipse82427.Leading,
      JointEllipse82427.DensityDelta, JointEllipse82427.Gap, JointEllipse82427.Upper,
      JointEllipse82427.Fraction, JointEllipse82427.X, JointEllipse82427.Y,
      JointEllipse82427.Linear, JointDensity82427.parameters, CoarseA, StrongA,
      BLocal, HLocal, LogLocal, RecoveryParameters291012.Lower, CovarianceScalar213.Polynomial]

theorem omitter_from_root {c L R : ℕ} {F : Finset (Finset ℤ)} {P T U : Finset ℤ}
    {tau : ℝ} (g : Start 82426 c L R F P T) (htau : tau≤1/2)
    (hd : RootQuadratic208.Q tau*(82426 : ℝ)^2<(RootCrooked F (c : ℤ)).card)
    (hUF : U∈F) (hbad : ¬IsAP U) (hcU : (c : ℤ)∉U) : tau*82426<U.card := by
  by_contra hnot
  have hsmall : (U.card : ℝ)≤tau*82426 := le_of_not_gt hnot
  let C := F.filter fun S => ¬IsAP S
  have hCF : C⊆F := Finset.filter_subset _ _
  have hCL : Legal (Ground 82426) C :=
    ⟨fun S hS => g.legal.1 S (hCF hS),
      fun S hS V hV hSV => g.legal.2 S (hCF hS) V (hCF hV) hSV⟩
  have hCB : ∀ S∈C, ¬IsAP S := fun S hS => (Finset.mem_filter.mp hS).2
  have hUC : U∈C := Finset.mem_filter.mpr ⟨hUF, hbad⟩
  have hroot : RootPart C (c : ℤ)=RootCrooked F (c : ℤ) := by
    ext S
    simp only [RootPart, C, RootCrooked, Finset.mem_filter]
    tauto
  have hsize : U.card+1≤82426 := by
    have hh : (U.card : ℝ)+1≤82426 := by linarith only [hsmall, htau]
    exact_mod_cast hh
  have hz : (U.card : ℝ)/(82426 : ℝ)≤tau := by
    apply (div_le_iff₀ (by norm_num : (0 : ℝ)<82426)).mpr
    simpa only [mul_comm] using hsmall
  have hq := RootQuadratic208.actual_normalized_root (by decide : 2≤82426)
    hCL hCB hUC hcU hsize hz (by linarith only [htau] : tau≤1)
  rw [hroot] at hq
  have hqR := (div_le_iff₀ (by norm_num : (0 : ℝ)<(82426 : ℝ)^2)).mp hq
  linarith only [hd, hqR]

theorem joint_omitter (i : Fin 2) {c L R : ℕ} {F : Finset (Finset ℤ)} {P T U : Finset ℤ}
    (g : Start 82426 c L R F P T) (hl : (L : ℝ)≤82426/2)
    (he : ((Omitted 82426 c F).card : ℝ)≤(JointDensity82427.parameters i).rho*82426)
    (hp : WidthProfile L (Width 82426 L R)≤(JointDensity82427.parameters i).A*82426+
      (JointDensity82427.parameters i).B*L+
      (JointDensity82427.parameters i).W*Width 82426 L R+(JointDensity82427.parameters i).C)
    (hUF : U∈F) (hbad : ¬IsAP U) (hcU : (c : ℤ)∉U) :
    (JointDensity82427.parameters i).tau*82426<U.card := by
  have caps := LocalRecovery82427.actual_caps (k := 0) (by decide)
    (by decide : 10000≤82426) (by decide : 82426≤High 0)
  have hc : (c : ℝ)≤L := by exact_mod_cast g.root_left.le
  have hm := mul_nonneg (sub_nonneg.mpr hc)
    (show 0≤(82426 : ℝ)+1-L-c by linarith only [hc, hl])
  have hh := mul_le_mul_of_nonneg_right caps.harmonic_le (by norm_num : (0 : ℝ)≤82426)
  have cert := joint_certificate i
  have hbound := JointEllipse82427.loss_bound (JointDensity82427.parameters i)
    cert.1 cert.2.1 cert.2.2.1 hp
  have hgap := cert.2.2.2.2.1
  have hd := DensityRecovery158375.root_density g (by decide : 1≤82426)
  have hstrict : RootQuadratic208.Q (JointDensity82427.parameters i).tau*(82426 : ℝ)^2<
      (RootCrooked F (c : ℤ)).card := by
    dsimp only [JointEllipse82427.Gap, JointEllipse82427.DensityDelta] at hgap
    norm_num only [RootQuadratic208.Q] at *
    nlinarith only [hm, hh, he, hd, hbound, hgap]
  exact omitter_from_root g (by fin_cases i <;> norm_num [JointDensity82427.parameters])
    hstrict hUF hbad hcU

theorem intermediate_omitter {c L R : ℕ} {F : Finset (Finset ℤ)} {P T U : Finset ℤ}
    (g : Start 82426 c L R F P T) (hl : (L : ℝ)<(17/250 : ℝ)*82426)
    (hw : Width 82426 L R<(14/125 : ℝ)*82426)
    (he : ((Omitted 82426 c F).card : ℝ)≤(223/25 : ℝ)*82426)
    (hUF : U∈F) (hbad : ¬IsAP U) (hcU : (c : ℤ)∉U) :
    (3/10 : ℝ)*82426<U.card := by
  have caps := LocalRecovery82427.actual_caps (k := 0) (by decide)
    (by decide : 10000≤82426) (by decide : 82426≤High 0)
  have hcL : (c : ℝ)≤L := by exact_mod_cast g.root_left.le
  have hc : (c : ℝ)≤(17/250 : ℝ)*82426 := hcL.trans hl.le
  have hm := mul_nonneg (sub_nonneg.mpr hc)
    (show 0≤(82426 : ℝ)-(17/250 : ℝ)*82426-c by linarith only [hc])
  have hw0 := width_nonnegative g
  have hw2 := mul_le_mul hw.le hw.le hw0 (by norm_num : (0 : ℝ)≤(14/125)*82426)
  have hh := mul_le_mul_of_nonneg_right caps.harmonic_le (by norm_num : (0 : ℝ)≤82426)
  have hd := DensityRecovery158375.root_density g (by decide : 1≤82426)
  apply omitter_from_root g (by norm_num : (3/10 : ℝ)≤1/2) ?_ hUF hbad hcU
  norm_num [HLocal, LogLocal, RootQuadratic208.Q] at hh ⊢
  nlinarith only [hm, hw2, hw.le, he, hh, hd]

theorem native_gate (k : Fin 7) :
    0≤NativeGates82427.Slope k ∧ 0<NativeGates82427.Slope k*82426-NativeGates82427.Centre k ∧
    NativeDual86412.Dual (NativeGates82427.U k) (NativeGates82427.V k)*
      (FineA 0*82426+ShiftEnergy (BLocal 0 18) (FineW 0) FineC) <
      (NativeGates82427.Slope k*82426-NativeGates82427.Centre k)^2 := by
  fin_cases k <;>
    norm_num [NativeGates82427.U, NativeGates82427.V, NativeGates82427.Slope,
      NativeGates82427.Constant, NativeGates82427.Centre, NativeDual86412.Dual,
      LeftCentre, WidthCentre, ShiftEnergy, FineA, FineW, FineC,
      BLocal, HLocal, LogLocal, RecoveryParameters291012.Lower, CovarianceScalar213.Polynomial]

theorem actual_direction {L w : ℝ}
    (hp : WidthProfile L w≤FineA 0*82426+BLocal 0 18*L+FineW 0*w+FineC) (k : Fin 7) :
    NativeGates82427.U k*L+NativeGates82427.V k*w+NativeGates82427.Constant k <
      NativeGates82427.Slope k*82426 := by
  have cert := native_gate k
  have he : NativeGates82427.Slope k*82426-NativeGates82427.Centre k =
      (NativeGates82427.Slope k*82426-NativeGates82427.Constant k)-
      (NativeGates82427.U k*LeftCentre (BLocal 0 18) (FineW 0)+
        NativeGates82427.V k*WidthCentre (BLocal 0 18) (FineW 0)) := by
    unfold NativeGates82427.Centre
    ring
  rw [he] at cert
  have hh := NativeDual86412.actual_dual_bound hp cert.2.1 cert.2.2
  linarith only [hh]

theorem native_from_profile {L R : ℕ} (hRN : R≤82426)
    (hwidth : 32*(L+82426-R)≤3*82426)
    (hp : WidthProfile L (Width 82426 L R) ≤ FineA 0*82426+BLocal 0 18*L+FineW 0*Width 82426 L R+FineC) :
    CoreSupply86412.Native 82426 L R := by
  let w := L+82426-R
  have hw : (w : ℝ)=Width 82426 L R := by
    dsimp only [w, Width]
    rw [Nat.cast_sub (by omega : R≤L+82426)]
    push_cast
    ring
  have h0 := actual_direction hp (0 : Fin 7)
  have h1 := actual_direction hp (1 : Fin 7)
  have h2 := actual_direction hp (2 : Fin 7)
  have h3 := actual_direction hp (3 : Fin 7)
  have h4 := actual_direction hp (4 : Fin 7)
  have h5 := actual_direction hp (5 : Fin 7)
  have h6 := actual_direction hp (6 : Fin 7)
  change (809 : ℝ)*L+1193*Width 82426 L R+6006<192*82426 at h0
  change (138 : ℝ)*L+93*Width 82426 L R+0<16*82426 at h1
  change (41 : ℝ)*L+19*Width 82426 L R+0<4*82426 at h2
  change (2 : ℝ)*L+(192/1001)*Width 82426 L R+0<(192/1001)*82426 at h3
  change (1 : ℝ)*L+(34/15)*Width 82426 L R+0<(4/15)*82426 at h4
  change (1 : ℝ)*L+1*Width 82426 L R+0<1*82426 at h5
  change (0 : ℝ)*L+3*Width 82426 L R+0<1*82426 at h6
  norm_num only [zero_mul, one_mul, add_zero, zero_add] at h0 h1 h2 h3 h4 h5 h6
  rw [←hw] at h0 h1 h2 h3 h4 h5 h6
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, hwidth⟩
  · exact_mod_cast h0
  · exact_mod_cast h1.le
  · exact_mod_cast h2.le
  · have h : (1001 : ℝ)*L+96*(w : ℝ)≤96*82426 := by nlinarith only [h3]
    exact_mod_cast h
  · have h : (15 : ℝ)*L+34*(w : ℝ)≤4*82426 := by nlinarith only [h4]
    exact_mod_cast h
  · exact_mod_cast h5.le
  · exact_mod_cast h6.le

#print axioms actual_count
#print axioms actual_deleted_count
#print axioms actual_omitted_count
#print axioms actual_quarter_count
#print axioms actual_three_tenths_count
#print axioms global_seventh
#print axioms coarse_local
#print axioms quarter_stage
#print axioms strong_stage
#print axioms fine_final
#print axioms joint_certificate
#print axioms omitter_from_root
#print axioms joint_omitter
#print axioms intermediate_omitter
#print axioms native_gate
#print axioms actual_direction
#print axioms native_from_profile
end
end JSP233.PointArithmetic82426
