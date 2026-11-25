module

public import Erdos272.Counting.N67702.RootJoint67702
public import Erdos272.Retention.N158375.DensityRecovery158375
public import Erdos272.Retention.N65968.RecoveryCertificates65968

@[expose] public section

namespace JSP233.JointDensity65968
open StarCompletion APGeometry HarmonicAbel29 RootModel291012 WitnessInterval43
open LocalRecovery65968 RecoveryCertificates65968 DensityRecovery158375
open scoped Classical
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1000000

def parameters : JointEllipse82427.Parameters :=
  { A := CoarseA 0, B := BLocal 0 7-1, W := GlobalW 0, C := 872
    rho := 1611/20, tau := 23/100, multiplier := 42 }
def Left : ℝ := 1/7

theorem monotonic_gate :
    0≤1-2*Left ∧ 0≤(1-2*Left)*63616+1-parameters.multiplier*2 := by
   norm_num [Left,parameters]

theorem certificate :
    JointEllipse82427.Certificate (parameters) (HLocal 0) 63616 := by

    norm_num [JointEllipse82427.Certificate, JointEllipse82427.U, JointEllipse82427.V,
      JointEllipse82427.Z, JointEllipse82427.Determinant, JointEllipse82427.Leading,
      JointEllipse82427.DensityDelta, JointEllipse82427.Gap, JointEllipse82427.Upper,
      JointEllipse82427.Fraction, JointEllipse82427.X, JointEllipse82427.Y,
      JointEllipse82427.Linear, parameters, CoarseA, GlobalW, BLocal, HLocal, LogLocal,
      RecoveryParameters291012.Lower, CovarianceScalar213.Polynomial]

theorem density_strict {n c L w e h root : ℝ}
    (hn : (63616 : ℝ)≤n) (hc : c≤L) (hL : L≤Left*n)
    (hh : h≤HLocal 0) (he : e≤(parameters).rho*n)
    (hp : Recovery208.WidthProfile L w≤
      (parameters).A*n+(parameters.B+2)*L+(parameters).W*w+parameters.C-2*c)
    (hd : 271/800*n^2-c*(n-c+1)-w^2/4-w-e-(h-1/2)*n≤root) :
    RootQuadratic208.Q (parameters).tau*n^2<root := by
  have hn0 : 0≤n := by linarith only [hn]
  have hm := monotonic_gate
  have hhmono := mul_le_mul_of_nonneg_left hn hm.1
  have hmono : 0≤n+1-parameters.multiplier*2-2*L := by
    nlinarith only [hhmono,hm.2,hL]
  have hhn := mul_le_mul_of_nonneg_right hh hn0
  have cert := certificate
  have hloss := RootJoint67702.loss_bound (parameters) (r:=2) cert.1 cert.2.1 cert.2.2.1 hc hmono hp
  have hgap := JointEllipse82427.gap_positive (parameters) cert hn
  dsimp only [JointEllipse82427.Gap, JointEllipse82427.DensityDelta] at hgap
  norm_num only [RootQuadratic208.Q] at *
  nlinarith only [hhn, he, hd, hloss, hgap]

theorem actual_omitter_size {N c L R k : ℕ} {F : Finset (Finset ℤ)} {P T U : Finset ℤ}
    (g : Start N c L R F P T) (hk : k<1) (hN : Low k ≤ N) (hhi : N ≤ High k)
    (hl : (L : ℝ)≤Left*N)
    (he : ((Omitted N c F).card : ℝ)≤(parameters).rho*N)
    (hp : Recovery208.WidthProfile L (Width N L R) ≤
      (parameters).A*N+(parameters.B+2)*L+(parameters).W*Width N L R+parameters.C-2*c)
    (hUF : U ∈ F) (hbad : ¬IsAP U) (hcU : (c : ℤ) ∉ U) :
    (parameters).tau*(N : ℝ)<U.card := by
  by_contra hnot
  have hbase := (low_bound k).trans hN
  have hn : (Low k : ℝ) ≤ N := by exact_mod_cast hN
  have hbig : (63616 : ℝ) ≤ N := by exact_mod_cast hbase
  have hNp : (0 : ℝ) < N := by linarith only [hbig]
  have hsmall : (U.card : ℝ)≤(parameters).tau*N := le_of_not_gt hnot
  have caps := LocalRecovery65968.actual_caps hk (by omega : 10000 ≤ N) hhi
  have hcleft : (c : ℝ) ≤ L := by exact_mod_cast g.root_left.le
  have hk0 : k=0 := by omega
  subst k
  have hd := density_strict hn hcleft hl caps.harmonic_le he hp
    (root_density g (by omega : 1≤N))
  let C := F.filter fun S => ¬IsAP S
  have hCF : C ⊆ F := Finset.filter_subset _ _
  have hCL : Legal (Ground N) C :=
    ⟨fun S hS => g.legal.1 S (hCF hS), fun S hS V hV hSV => g.legal.2 S (hCF hS) V (hCF hV) hSV⟩
  have hCB : ∀ S ∈ C, ¬IsAP S := fun S hS => (Finset.mem_filter.mp hS).2
  have hUC : U ∈ C := Finset.mem_filter.mpr ⟨hUF, hbad⟩
  have hroot : RootPart C (c : ℤ) = RootCrooked F (c : ℤ) := by
    ext S
    simp only [RootPart, C, RootCrooked, Finset.mem_filter]
    tauto
  have htau : (parameters).tau≤1/2 := by  norm_num [parameters]
  have htauN := mul_le_mul_of_nonneg_right htau hNp.le
  have hsize : U.card+1 ≤ N := by
    have hh : (U.card : ℝ)+1 ≤ N := by linarith only [hsmall, htauN, hbig]
    exact_mod_cast hh
  have hz : (U.card : ℝ)/(N : ℝ)≤(parameters).tau := (div_le_iff₀ hNp).mpr hsmall
  have hq := RootQuadratic208.actual_normalized_root (by omega : 2 ≤ N) hCL hCB hUC hcU hsize hz
    (htau.trans (by norm_num : (1/2 : ℝ)≤1))
  rw [hroot] at hq
  have hqR := (div_le_iff₀ (sq_pos_of_pos hNp)).mp hq
  linarith only [hd, hqR]

#print axioms monotonic_gate
#print axioms certificate
#print axioms density_strict
#print axioms actual_omitter_size
end
end JSP233.JointDensity65968
