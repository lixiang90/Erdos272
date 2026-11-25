module

public import Erdos272.Resources.N158375.LocalRecovery158375
public import Erdos272.Retention.N291012.UnitAvoider291012
public import Erdos272.Resources.DenseOmitted214

@[expose] public section

namespace JSP233.DensityRecovery158375
open StarCompletion APGeometry APCount41 DenseDeletion40 HarmonicAbel29 WitnessInterval43
open RootModel291012 UnitCount218 PairShadowBudget218 LocalRecovery158375
open scoped Classical
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1000000

def Delta (tau left v : ℝ) : ℝ :=
  271/800-left*(1-left)-v^2/4-RootQuadratic208.Q tau

def Loss (left v alpha beta : ℝ) : ℝ := HLocal-1/2+left+v+alpha+beta*v

def Gate (tau left v alpha beta constant : ℝ) : Prop :=
  0 ≤ left ∧ left ≤ 1/2 ∧ 0 ≤ v ∧ 0 ≤ beta ∧ 0 < Delta tau left v ∧
    0 < Delta tau left v*155000-Loss left v alpha beta-max constant 0/155000

theorem quarter_gate : Gate (1/4) (3/25) (49/250) 144 0 1296 := by
  norm_num [Gate, Delta, Loss, HLocal, RootQuadratic208.Q]

theorem third_gate : Gate (1/3) (1/18) (1/10) 17 0 0 := by
  norm_num [Gate, Delta, Loss, HLocal, RootQuadratic208.Q]

theorem actual_root_unit_count {N c L R : ℕ} {F : Finset (Finset ℤ)} {P T : Finset ℤ}
    (g : Start N c L R F P T) :
    ((RootUnitAP F (c : ℤ)).card : ℝ) ≤ (c : ℝ)*((N : ℝ)-c+1) := by
  let U := RootUnitAP F (c : ℤ)
  have hsub : U ⊆ F := Finset.filter_subset _ _
  have hlegal : Legal (Ground N) U :=
    ⟨fun S hS => g.legal.1 S (hsub hS), fun S hS V hV hSV => g.legal.2 S (hsub hS) V (hsub hV) hSV⟩
  have hb := actual_same_step_rectangle (d := 1) (by decide) g.root_mem hlegal
    (fun S hS => (Finset.mem_filter.mp hS).2.1) (by
      intro S hS
      obtain ⟨_hSF, _hcS, hAP, _htwo, hstep⟩ := Finset.mem_filter.mp hS
      obtain ⟨_hd, p, hp⟩ := actual_step hAP
      exact ⟨p, by simpa only [hstep, Nat.cast_one] using hp⟩)
  have hc := (mem_ground N (c : ℤ)).mp g.root_mem
  have ha : ((c : ℤ)-1).toNat+1=c := by omega
  have hz : ((N : ℤ)-(c : ℤ)).toNat=N-c := by omega
  simp only [Nat.div_one, ha, hz] at hb
  have hr : (U.card : ℝ) ≤ (c : ℝ)*((N-c+1 : ℕ) : ℝ) := by exact_mod_cast hb
  have hcN : c ≤ N := by exact_mod_cast hc.2
  simpa only [Nat.cast_add, Nat.cast_sub hcN, Nat.cast_one] using hr

theorem root_density {N c L R : ℕ} {F : Finset (Finset ℤ)} {P T : Finset ℤ}
    (g : Start N c L R F P T) (hN : 1 ≤ N) :
    271/800*(N : ℝ)^2-(c : ℝ)*((N : ℝ)-c+1)-(Width N L R)^2/4-
      Width N L R-(Omitted N c F).card-(Harmonic N-1/2)*N ≤
      (RootCrooked F (c : ℤ)).card := by
  have ha := actual_AP_count hN g.legal
  have hf : ((RootCrooked F (c : ℤ)).card : ℝ)+(Omitted N c F).card+(F.filter IsAP).card = F.card := by
    exact_mod_cast family_partition g.root
  have hu : ((RootUnitAP F (c : ℤ)).card : ℝ)+(AvoidUnitAP F (c : ℤ)).card = (UnitAP F).card := by
    exact_mod_cast unit_partition F (c : ℤ)
  have hr := actual_root_unit_count g
  have hv := UnitAvoider291012.actual_avoid_unit_width_count g
  have hn : (N.choose 2 : ℝ)+1 ≤ F.card := by
    exact_mod_cast (show N.choose 2+1 ≤ F.card by have h := g.near_card; unfold B at h; omega)
  rw [Nat.cast_choose_two] at hn
  dsimp only [Width]
  nlinarith only [ha, hf, hu, hr, hv, hn]

theorem density_strict {n c w e h root tau left v alpha beta constant : ℝ}
    (hn : 155000 ≤ n) (hc0 : 0 ≤ c) (hc : c ≤ left*n)
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
  have hlin : 0 < Delta tau left v*n-Loss left v alpha beta-max constant 0/155000 := by
    linarith only [hgate, hdelta]
  have hcfee0 : 0 ≤ max constant 0 := le_max_right _ _
  have hcfee := mul_le_mul_of_nonneg_left hn (div_nonneg hcfee0 (by norm_num : (0 : ℝ) ≤ 155000))
  have hcfee' : constant ≤ max constant 0 := le_max_left _ _
  have hpay := mul_pos hlin hn0
  dsimp only [Delta, Loss] at hpay
  nlinarith only [hp, hc, hw2, hw.le, hbw, hhn, hd, he, hcfee, hcfee', hpay]

theorem actual_omitter_size {N c L R : ℕ} {F : Finset (Finset ℤ)} {P T U : Finset ℤ}
    {tau left v alpha beta constant : ℝ}
    (g : Start N c L R F P T) (hN : 158375 ≤ N) (hhi : N ≤ 179999)
    (hl : (L : ℝ) < left*N) (hw : Width N L R < v*N)
    (he : ((Omitted N c F).card : ℝ) ≤ alpha*N+beta*Width N L R+constant)
    (hg : Gate tau left v alpha beta constant) (htau : tau ≤ 1/2)
    (hUF : U ∈ F) (hbad : ¬IsAP U) (hcU : (c : ℤ) ∉ U) : tau*(N : ℝ) < U.card := by
  by_contra hnot
  have hn : (155000 : ℝ) ≤ N := by exact_mod_cast (show 155000 ≤ N by omega)
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
#print axioms actual_root_unit_count
#print axioms root_density
#print axioms density_strict
#print axioms actual_omitter_size
end
end JSP233.DensityRecovery158375
