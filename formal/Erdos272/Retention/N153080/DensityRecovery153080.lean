module

public import Erdos272.Retention.N158375.DensityRecovery158375

@[expose] public section

namespace JSP233.DensityRecovery153080
open StarCompletion APGeometry APCount41 DenseDeletion40 HarmonicAbel29 WitnessInterval43
open RootModel291012 UnitCount218 PairShadowBudget218 LocalRecovery158375 DensityRecovery158375
open scoped Classical
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1000000

def Gate (tau left v alpha beta constant : ℝ) : Prop :=
  0 ≤ left ∧ left ≤ 1/2 ∧ 0 ≤ v ∧ 0 ≤ beta ∧ 0 < Delta tau left v ∧
    0 < Delta tau left v*151879-Loss left v alpha beta-max constant 0/151879

theorem quarter_gate : Gate (1/4) (3/25) (49/250) 144 0 1296 := by
  norm_num [Gate, Delta, Loss, HLocal, RootQuadratic208.Q]

theorem third_gate : Gate (1/3) (1/18) (1/10) 17 0 0 := by
  norm_num [Gate, Delta, Loss, HLocal, RootQuadratic208.Q]

theorem density_strict {n c w e h root tau left v alpha beta constant : ℝ}
    (hn : 151879 ≤ n) (hc0 : 0 ≤ c) (hc : c ≤ left*n)
    (hw0 : 0 ≤ w) (hw : w < v*n) (hh : h ≤ HLocal)
    (he : e ≤ alpha*n+beta*w+constant)
    (hd : 271/800*n^2-c*(n-c+1)-w^2/4-w-e-(h-1/2)*n ≤ root)
    (hg : Gate tau left v alpha beta constant) : RootQuadratic208.Q tau*n^2 < root := by
  obtain ⟨hl0, hlhalf, hv0, hb0, hdelta0, hgate⟩ := hg
  have hn0 : 0 < n := by linarith only [hn]
  have hlhalfN := mul_le_mul_of_nonneg_right hlhalf hn0.le
  have hother : 0 ≤ n-left*n-c := by nlinarith only [hc, hlhalfN]
  have hp := mul_nonneg (sub_nonneg.mpr hc) hother
  have hw2 := mul_le_mul hw.le hw.le hw0 (mul_nonneg hv0 hn0.le)
  have hbw := mul_le_mul_of_nonneg_left hw.le hb0
  have hhn := mul_le_mul_of_nonneg_right hh hn0.le
  have hdelta := mul_le_mul_of_nonneg_left hn hdelta0.le
  have hlin : 0 < Delta tau left v*n-Loss left v alpha beta-max constant 0/151879 := by
    linarith only [hgate, hdelta]
  have hcfee0 : 0 ≤ max constant 0 := le_max_right _ _
  have hcfee := mul_le_mul_of_nonneg_left hn (div_nonneg hcfee0 (by norm_num : (0 : ℝ) ≤ 151879))
  have hcfee' : constant ≤ max constant 0 := le_max_left _ _
  have hpay := mul_pos hlin hn0
  dsimp only [Delta, Loss] at hpay
  nlinarith only [hp, hc, hw2, hw.le, hbw, hhn, hd, he, hcfee, hcfee', hpay]

theorem actual_omitter_size {N c L R : ℕ} {F : Finset (Finset ℤ)} {P T U : Finset ℤ}
    {tau left v alpha beta constant : ℝ}
    (g : Start N c L R F P T) (hN : 151879 ≤ N) (hhi : N ≤ 179999)
    (hl : (L : ℝ) < left*N) (hw : Width N L R < v*N)
    (he : ((Omitted N c F).card : ℝ) ≤ alpha*N+beta*Width N L R+constant)
    (hg : Gate tau left v alpha beta constant) (htau : tau ≤ 1/2)
    (hUF : U ∈ F) (hbad : ¬IsAP U) (hcU : (c : ℤ) ∉ U) : tau*(N : ℝ) < U.card := by
  by_contra hnot
  have hn : (151879 : ℝ) ≤ N := by exact_mod_cast (show 151879 ≤ N by omega)
  have hNp : (0 : ℝ) < N := by linarith only [hn]
  have hsmall : (U.card : ℝ) ≤ tau*N := le_of_not_gt hnot
  have caps := LocalRecovery158375.actual_caps (by omega : 100000 ≤ N) hhi
  have hcleft : (c : ℝ) ≤ left*N := by
    have hcL : (c : ℝ) < L := by exact_mod_cast g.root_left
    linarith only [hcL, hl]
  have hd := density_strict hn (Nat.cast_nonneg c) hcleft (width_nonnegative g) hw
    caps.harmonic_le he (root_density g (by omega : 1 ≤ N)) hg
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

#print axioms quarter_gate
#print axioms third_gate
#print axioms density_strict
#print axioms actual_omitter_size
end
end JSP233.DensityRecovery153080
