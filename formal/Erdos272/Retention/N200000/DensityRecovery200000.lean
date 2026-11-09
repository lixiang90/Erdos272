module

public import Erdos272.Retention.N233811.DensityRecovery233811
public import Erdos272.Retention.N291012.UnitAvoider291012
public import Erdos272.Geometry.PairShadowGeometry218
public import Erdos272.Resources.DenseOmitted214

@[expose] public section

namespace JSP233.DensityRecovery200000
open StarCompletion APGeometry DenseDeletion40 HarmonicAbel29 WitnessInterval43
open RootModel291012 RecoveryCaps213 PairShadowBudget218 PairShadowGeometry218 UnitCount218
open DensityRecovery233811 (root_density)
open scoped Classical
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1000000

def Delta (tau v : ℝ) : ℝ := 71/400-v^2/2-RootQuadratic208.Q tau

def Loss (v alpha beta : ℝ) : ℝ := 2*HCap+2*v+2*alpha+2*beta*v

def Gate (tau v alpha beta constant : ℝ) : Prop :=
  0 ≤ v ∧ 0 ≤ beta ∧ 0 < Delta tau v ∧
    0 < Delta tau v*200000-Loss v alpha beta-max (2*constant-3/2) 0/200000

theorem coarse_gate : Gate (1/6) (1/5) 144 0 1296 := by
  norm_num [Gate, Delta, Loss, HCap, LogCap, RootQuadratic208.Q]

theorem strong_gate : Gate (189/1000) (51/500) (3601/100) 0 0 := by
  norm_num [Gate, Delta, Loss, HCap, LogCap, RootQuadratic208.Q]

theorem density_strict {n w e h root tau v alpha beta constant : ℝ}
    (hn : 200000 ≤ n) (hw0 : 0 ≤ w) (hw : w < v*n)
    (hh : h ≤ HCap) (he : e ≤ alpha*n+beta*w+constant)
    (hd : 71/400*n^2-w^2/2-2*w-2*e-2*h*n+3/2 ≤ root)
    (hg : Gate tau v alpha beta constant) : RootQuadratic208.Q tau*n^2 < root := by
  have hn0 : 0 < n := by linarith only [hn]
  have hw2 := mul_le_mul hw.le hw.le hw0 (mul_nonneg hg.1 hn0.le)
  have hbw := mul_le_mul_of_nonneg_left hw.le hg.2.1
  have hhn := mul_le_mul_of_nonneg_right hh hn0.le
  have hdelta := mul_le_mul_of_nonneg_left hn hg.2.2.1.le
  have hlin : 0 < Delta tau v*n-Loss v alpha beta-max (2*constant-3/2) 0/200000 := by
    linarith only [hg.2.2.2, hdelta]
  have hc0 : 0 ≤ max (2*constant-3/2) 0 := le_max_right _ _
  have hcN := mul_le_mul_of_nonneg_left hn (div_nonneg hc0 (by norm_num : (0 : ℝ) ≤ 200000))
  have hcx : 2*constant-3/2 ≤ max (2*constant-3/2) 0 := le_max_left _ _
  have hp := mul_pos hlin hn0
  dsimp only [Delta, Loss] at hp
  nlinarith only [hw2, hbw, hhn, hd, he, hcN, hcx, hp, hw.le]

theorem actual_omitter_size {N c L R : ℕ} {F : Finset (Finset ℤ)} {P T U : Finset ℤ}
    {tau v alpha beta constant : ℝ}
    (g : Start N c L R F P T) (hN : 200000 ≤ N) (hhi : N ≤ 642498)
    (hw : Width N L R < v*(N : ℝ))
    (he : ((Omitted N c F).card : ℝ) ≤ alpha*N+beta*Width N L R+constant)
    (hg : Gate tau v alpha beta constant) (htau : tau ≤ 1/2)
    (hUF : U ∈ F) (hbad : ¬IsAP U) (hcU : (c : ℤ) ∉ U) : tau*(N : ℝ) < U.card := by
  by_contra hnot
  have hn : (200000 : ℝ) ≤ N := by exact_mod_cast hN
  have hNp : (0 : ℝ) < N := by linarith only [hn]
  have hsmall : (U.card : ℝ) ≤ tau*N := le_of_not_gt hnot
  have caps := actual_caps (by omega : 100000 ≤ N) (by omega : N ≤ 656184)
  have hd := density_strict hn (width_nonnegative g) hw caps.harmonic_le he
    (root_density g (by omega : 2 ≤ N)) hg
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
    have ht := mul_le_mul_of_nonneg_right htau hNp.le
    have hh : (U.card : ℝ)+1 ≤ N := by linarith only [hsmall, ht, hn]
    exact_mod_cast hh
  have hz : (U.card : ℝ)/(N : ℝ) ≤ tau := (div_le_iff₀ hNp).mpr hsmall
  have hq := RootQuadratic208.actual_normalized_root (by omega : 2 ≤ N) hCL hCB hUC hcU hsize hz
    (by linarith only [htau] : tau ≤ 1)
  rw [hroot] at hq
  have hqR := (div_le_iff₀ (sq_pos_of_pos hNp)).mp hq
  linarith only [hd, hqR]

#print axioms coarse_gate
#print axioms strong_gate
#print axioms density_strict
#print axioms actual_omitter_size
end
end JSP233.DensityRecovery200000
