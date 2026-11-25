module

public import Erdos272.Counting.N82427.JointEllipse82427
public import Erdos272.Retention.N158375.DensityRecovery158375
public import Erdos272.Retention.N80470.RecoveryCertificates80470

@[expose] public section

namespace JSP233.JointDensity80470
open StarCompletion APGeometry HarmonicAbel29 RootModel291012 WitnessInterval43
open LocalRecovery80470 RecoveryCertificates80470 DensityRecovery158375
open scoped Classical
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1000000

def parameters (i : Fin 3) : JointEllipse82427.Parameters :=
  { A := if i=0 then CoarseA 0 else if i=1 then MiddleA 0 else StrongA 0
    B := if i=0 then BLocal 0 7 else if i=1 then BLocal 0 15 else BLocal 0 16
    W := HLocal 0
    C := 872
    rho := if i=0 then 1609/20 else if i=1 then 1239/200 else 109/20
    tau := if i=0 then 31/125 else if i=1 then 8/25 else 1/3
    multiplier := if i=0 then 46 else if i=1 then 99 else 101 }

theorem certificate (i : Fin 3) :
    JointEllipse82427.Certificate (parameters i) (HLocal 0) 80470 := by
  fin_cases i <;>
    norm_num [JointEllipse82427.Certificate, JointEllipse82427.U, JointEllipse82427.V,
      JointEllipse82427.Z, JointEllipse82427.Determinant, JointEllipse82427.Leading,
      JointEllipse82427.DensityDelta, JointEllipse82427.Gap, JointEllipse82427.Upper,
      JointEllipse82427.Fraction, JointEllipse82427.X, JointEllipse82427.Y,
      JointEllipse82427.Linear, parameters, CoarseA, MiddleA, StrongA, BLocal, HLocal, LogLocal,
      RecoveryParameters291012.Lower, CovarianceScalar213.Polynomial]

theorem density_strict (i : Fin 3) {n c L w e h root : ℝ}
    (hn : (80470 : ℝ)≤n) (hc : c≤L) (hL : L≤n/2)
    (hh : h≤HLocal 0) (he : e≤(parameters i).rho*n)
    (hp : Recovery208.WidthProfile L w≤
      (parameters i).A*n+(parameters i).B*L+(parameters i).W*w+(parameters i).C)
    (hd : 271/800*n^2-c*(n-c+1)-w^2/4-w-e-(h-1/2)*n≤root) :
    RootQuadratic208.Q (parameters i).tau*n^2<root := by
  have hn0 : 0≤n := by linarith only [hn]
  have hmono := mul_nonneg (sub_nonneg.mpr hc)
    (show 0≤n+1-L-c by linarith only [hc, hL])
  have hhn := mul_le_mul_of_nonneg_right hh hn0
  have cert := certificate i
  have hloss := JointEllipse82427.loss_bound (parameters i) cert.1 cert.2.1 cert.2.2.1 hp
  have hgap := JointEllipse82427.gap_positive (parameters i) cert hn
  dsimp only [JointEllipse82427.Gap, JointEllipse82427.DensityDelta] at hgap
  norm_num only [RootQuadratic208.Q] at *
  nlinarith only [hmono, hhn, he, hd, hloss, hgap]

theorem actual_omitter_size (i : Fin 3) {N c L R k : ℕ} {F : Finset (Finset ℤ)} {P T U : Finset ℤ}
    (g : Start N c L R F P T) (hk : k<1) (hN : Low k ≤ N) (hhi : N ≤ High k)
    (hl : (L : ℝ)≤(N : ℝ)/2)
    (he : ((Omitted N c F).card : ℝ)≤(parameters i).rho*N)
    (hp : Recovery208.WidthProfile L (Width N L R) ≤
      (parameters i).A*N+(parameters i).B*L+(parameters i).W*Width N L R+(parameters i).C)
    (hUF : U ∈ F) (hbad : ¬IsAP U) (hcU : (c : ℤ) ∉ U) :
    (parameters i).tau*(N : ℝ)<U.card := by
  by_contra hnot
  have hbase := (low_bound k).trans hN
  have hn : (Low k : ℝ) ≤ N := by exact_mod_cast hN
  have hbig : (80470 : ℝ) ≤ N := by exact_mod_cast hbase
  have hNp : (0 : ℝ) < N := by linarith only [hbig]
  have hsmall : (U.card : ℝ)≤(parameters i).tau*N := le_of_not_gt hnot
  have caps := LocalRecovery80470.actual_caps hk (by omega : 10000 ≤ N) hhi
  have hcleft : (c : ℝ) ≤ L := by exact_mod_cast g.root_left.le
  have hk0 : k=0 := by omega
  subst k
  have hd := density_strict i hn hcleft hl caps.harmonic_le he hp
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
  have htau : (parameters i).tau≤1/2 := by fin_cases i <;> norm_num [parameters]
  have htauN := mul_le_mul_of_nonneg_right htau hNp.le
  have hsize : U.card+1 ≤ N := by
    have hh : (U.card : ℝ)+1 ≤ N := by linarith only [hsmall, htauN, hbig]
    exact_mod_cast hh
  have hz : (U.card : ℝ)/(N : ℝ)≤(parameters i).tau := (div_le_iff₀ hNp).mpr hsmall
  have hq := RootQuadratic208.actual_normalized_root (by omega : 2 ≤ N) hCL hCB hUC hcU hsize hz
    (htau.trans (by norm_num : (1/2 : ℝ)≤1))
  rw [hroot] at hq
  have hqR := (div_le_iff₀ (sq_pos_of_pos hNp)).mp hq
  linarith only [hd, hqR]

#print axioms certificate
#print axioms density_strict
#print axioms actual_omitter_size
end
end JSP233.JointDensity80470
