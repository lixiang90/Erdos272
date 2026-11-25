module

public import Erdos272.Retention.N158375.DensityRecovery158375
public import Erdos272.Resources.N65968.LocalRecovery65968

@[expose] public section

namespace JSP233.DensityRecovery65968
open StarCompletion APGeometry APCount41 DenseDeletion40 HarmonicAbel29 WitnessInterval43
open RootModel291012 UnitCount218 PairShadowBudget218 LocalRecovery65968 DensityRecovery158375
open scoped Classical
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1000000

def Delta (tau left v : ℝ) : ℝ := 271/800-left*(1-left)-v^2/4-RootQuadratic208.Q tau
def Loss (k : ℕ) (left v alpha beta : ℝ) : ℝ := HLocal k-1/2+left+v+alpha+beta*v
def Gate (k : ℕ) (tau left v alpha beta constant : ℝ) : Prop :=
  0 ≤ left ∧ left ≤ 1/2 ∧ 0 ≤ v ∧ 0 ≤ beta ∧ 0 < Delta tau left v ∧
    0 < Delta tau left v*(Low k)-Loss k left v alpha beta-max constant 0/(Low k)

theorem intermediate_gate {k : ℕ} (hk : k<1) : Gate k (61/200) (1/13) (1/8) (53/5) 0 0 := by
  interval_cases k <;>
    norm_num [Gate, Delta, Loss, HLocal, LogLocal, LocalRecovery65968.Low, RootQuadratic208.Q]

theorem strong_gate {k : ℕ} (hk : k<1) :
    Gate k (1/3) (3/50) (51/500) 0 (53/6) (-13/2) := by
  interval_cases k <;>
    norm_num [Gate,Delta,Loss,HLocal,LogLocal,LocalRecovery65968.Low,RootQuadratic208.Q]
#print axioms strong_gate

theorem density_strict {k : ℕ} {n c w e h root tau left v alpha beta constant : ℝ}
    (hn : (Low k : ℝ) ≤ n) (_hc0 : 0 ≤ c) (hc : c ≤ left*n)
    (hw0 : 0 ≤ w) (hw : w < v*n) (hh : h ≤ HLocal k)
    (he : e ≤ alpha*n+beta*w+constant)
    (hd : 271/800*n^2-c*(n-c+1)-w^2/4-w-e-(h-1/2)*n ≤ root)
    (hg : Gate k tau left v alpha beta constant) : RootQuadratic208.Q tau*n^2 < root := by
  obtain ⟨hl0, hlhalf, hv0, hb0, hdelta0, hgate⟩ := hg
  have hlo : (0 : ℝ) < Low k := by
    exact_mod_cast (show 0 < Low k by have hb := low_bound k; omega)
  have hn0 : 0 < n := hlo.trans_le hn
  have hlhalfN := mul_le_mul_of_nonneg_right hlhalf hn0.le
  have hother : 0 ≤ n-left*n-c := by nlinarith only [hc, hlhalfN]
  have hp := mul_nonneg (sub_nonneg.mpr hc) hother
  have hw2 := mul_le_mul hw.le hw.le hw0 (mul_nonneg hv0 hn0.le)
  have hbw := mul_le_mul_of_nonneg_left hw.le hb0
  have hhn := mul_le_mul_of_nonneg_right hh hn0.le
  have hdelta := mul_le_mul_of_nonneg_left hn hdelta0.le
  have hlin : 0 < Delta tau left v*n-Loss k left v alpha beta-max constant 0/(Low k) := by
    linarith only [hgate, hdelta]
  have hcfee0 : 0 ≤ max constant 0 := le_max_right _ _
  have hcfee := mul_le_mul_of_nonneg_left hn (div_nonneg hcfee0 hlo.le)
  have hcancel : max constant 0/(Low k)*(Low k : ℝ) = max constant 0 :=
    div_mul_cancel₀ _ hlo.ne'
  have hcfee' : constant ≤ max constant 0 := le_max_left _ _
  have hpay := mul_pos hlin hn0
  dsimp only [Delta, Loss] at hpay
  nlinarith only [hp, hc, hw2, hw.le, hbw, hhn, hd, he, hcfee, hcancel, hcfee', hpay]

theorem actual_omitter_size {N c L R k : ℕ} {F : Finset (Finset ℤ)} {P T U : Finset ℤ}
    {tau left v alpha beta constant : ℝ}
    (g : Start N c L R F P T) (hk : k<1) (hN : Low k ≤ N) (hhi : N ≤ High k)
    (hl : (L : ℝ) < left*N) (hw : Width N L R < v*N)
    (he : ((Omitted N c F).card : ℝ) ≤ alpha*N+beta*Width N L R+constant)
    (hg : Gate k tau left v alpha beta constant) (htau : tau ≤ 1/2)
    (hUF : U ∈ F) (hbad : ¬IsAP U) (hcU : (c : ℤ) ∉ U) : tau*(N : ℝ) < U.card := by
  by_contra hnot
  have hbase := (low_bound k).trans hN
  have hn : (Low k : ℝ) ≤ N := by exact_mod_cast hN
  have hbig : (63616 : ℝ) ≤ N := by exact_mod_cast hbase
  have hNp : (0 : ℝ) < N := by linarith only [hbig]
  have hsmall : (U.card : ℝ) ≤ tau*N := le_of_not_gt hnot
  have caps := LocalRecovery65968.actual_caps hk (by omega : 10000 ≤ N) hhi
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
    have hh : (U.card : ℝ)+1 ≤ N := by linarith only [hsmall, ht, hbig]
    exact_mod_cast hh
  have hz : (U.card : ℝ)/(N : ℝ) ≤ tau := (div_le_iff₀ hNp).mpr hsmall
  have hq := RootQuadratic208.actual_normalized_root (by omega : 2 ≤ N) hCL hCB hUC hcU hsize hz
    (by linarith only [htau] : tau ≤ 1)
  rw [hroot] at hq
  have hqR := (div_le_iff₀ (sq_pos_of_pos hNp)).mp hq
  linarith only [hd, hqR]

#print axioms intermediate_gate
#print axioms density_strict
#print axioms actual_omitter_size
end
end JSP233.DensityRecovery65968
