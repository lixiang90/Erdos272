module

public import Erdos272.Counting.N109474.JointEllipse109474
public import Erdos272.Retention.N109474.DensityRecovery109474

@[expose] public section

namespace JSP233.JointDensity109474
open StarCompletion APGeometry HarmonicAbel29 RootModel291012 WitnessInterval43
open LocalRecovery118533 RecoveryCertificates109474 DensityRecovery158375
open scoped Classical
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1000000

theorem density_strict {n c L w e h root : ℝ}
    (hn : 109474 ≤ n) (hc : c ≤ L) (hL : L ≤ n/2)
    (hh : h ≤ HLocal) (he : e ≤ (19/2 : ℝ)*n)
    (hp : Recovery208.WidthProfile L w ≤ StrongA*n+BLocal 16*L+HLocal*w+872)
    (hd : 271/800*n^2-c*(n-c+1)-w^2/4-w-e-(h-1/2)*n ≤ root) :
    RootQuadratic208.Q (1/3)*n^2 < root := by
  have hmono := mul_nonneg (sub_nonneg.mpr hc)
    (show 0 ≤ n+1-L-c by linarith only [hc, hL])
  have hhn := mul_le_mul_of_nonneg_right hh (show 0 ≤ n by linarith only [hn])
  have hloss := JointEllipse109474.loss_bound hp
  have hgap := JointEllipse109474.gap_positive hn
  dsimp only [JointEllipse109474.Gap] at hgap
  norm_num only [RootQuadratic208.Q] at *
  nlinarith only [hmono, hhn, he, hd, hloss, hgap]

theorem actual_omitter_size {N c L R : ℕ} {F : Finset (Finset ℤ)} {P T U : Finset ℤ}
    (g : Start N c L R F P T) (hN : 109474 ≤ N) (hhi : N ≤ 118532)
    (hl : (L : ℝ) < (1/16 : ℝ)*N)
    (he : ((Omitted N c F).card : ℝ) ≤ (19/2 : ℝ)*N)
    (hp : Recovery208.WidthProfile L (Width N L R) ≤
      StrongA*N+BLocal 16*L+HLocal*Width N L R+872)
    (hUF : U ∈ F) (hbad : ¬IsAP U) (hcU : (c : ℤ) ∉ U) :
    (1/3 : ℝ)*(N : ℝ) < U.card := by
  by_contra hnot
  have hn : (109474 : ℝ) ≤ N := by exact_mod_cast hN
  have hNp : (0 : ℝ) < N := by linarith only [hn]
  have hsmall : (U.card : ℝ) ≤ (1/3 : ℝ)*N := le_of_not_gt hnot
  have caps := LocalRecovery118533.actual_caps (by omega : 100000 ≤ N) (by omega : N ≤ 129999)
  have hcleft : (c : ℝ) ≤ L := by exact_mod_cast g.root_left.le
  have hd := density_strict hn hcleft (by linarith only [hl, hNp])
    caps.harmonic_le he hp (root_density g (by omega : 1 ≤ N))
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
  have hsize : U.card+1 ≤ N := by
    have hh : (U.card : ℝ)+1 ≤ N := by linarith only [hsmall, hn]
    exact_mod_cast hh
  have hz : (U.card : ℝ)/(N : ℝ) ≤ (1/3 : ℝ) := (div_le_iff₀ hNp).mpr hsmall
  have hq := RootQuadratic208.actual_normalized_root (by omega : 2 ≤ N) hCL hCB hUC hcU hsize hz
    (by norm_num : (1/3 : ℝ) ≤ 1)
  rw [hroot] at hq
  have hqR := (div_le_iff₀ (sq_pos_of_pos hNp)).mp hq
  linarith only [hd, hqR]

#print axioms density_strict
#print axioms actual_omitter_size
end
end JSP233.JointDensity109474
