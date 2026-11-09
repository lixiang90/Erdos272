module

public import Erdos272.Arithmetic.UniformPolynomial208
public import Erdos272.Resources.UniformActual208
public import Mathlib.Algebra.Order.Archimedean.Real.Basic

@[expose] public section

/-! The complete high-density side is monotone across every closed step boundary. -/
namespace JSP233.UniformHigh208
open UniformSourceCore208 UniformPolynomial208 UniformActual208 StepWeightShape208 NeighborMass208
noncomputable section
set_option maxHeartbeats 0

def QH (y z M : ℝ) : ℝ := z*(y-1-7*M/25)+
  (3*z-y-1)/2*(y-2-14*M/25)+(5*z-2*y-2)/3*(y-3-21*M/25)

def QD (y z M : ℝ) : ℝ := 25*z/6-7*y/3+21*M/25+11/6

def RP (D : ℕ) (y z M : ℝ) : ℝ := QH y z M+160/M*JP D y z

theorem QH_difference (a b z M : ℝ) :
    QH b z M-QH a z M=(b-a)*(QD a z M+QD b z M)/2 := by unfold QH QD;ring

theorem QD_pos {y z M : ℝ} (hM : 31≤M) (hy : y≤2*z) (hz : z≤4*M/5) :
    0<QD y z M := by unfold QD;linarith only [hM,hy,hz]

theorem RP_mono_cell {D : ℕ} {a b z M : ℝ} (hD : 2≤D) (hM : 31≤M)
    (ha : M≤a) (hab : a≤b) (hb : b≤2*z) (hz : z≤4*M/5)
    (hca : (D : ℝ)*(a-z)≤a) (hcb : (D : ℝ)*(b-z)≤b) : RP D a z M≤RP D b z M := by
  have hq1 := QD_pos hM (hab.trans hb) hz
  have hq2 := QD_pos hM hb hz
  have hq : QH a z M≤QH b z M := by
    have hh := mul_nonneg (sub_nonneg.mpr hab) (by linarith only [hq1,hq2] : 0≤QD a z M+QD b z M)
    have hid := QH_difference a b z M
    linarith only [hh,hid]
  have hj := mul_le_mul_of_nonneg_left (JP_mono_cell hD (hM.trans ha) hab hca hcb)
    (by positivity : 0≤160/M)
  exact add_le_add hq hj

theorem RP_boundary (D : ℕ) (hD : 1≤D) (z M : ℝ) :
    RP (D+1) (((D : ℝ)+1)*z/(D : ℝ)) z M=RP D (((D : ℝ)+1)*z/(D : ℝ)) z M := by
  unfold RP
  rw [JP_boundary D hD]

theorem RP_cross (D : ℕ) : ∀ E : ℕ,∀ a b z M : ℝ,
    2≤E → E≤D → 31≤M → M≤a → a≤b → b≤2*z → z≤4*M/5 →
    (D : ℝ)*(a-z)≤a → a≤((D : ℝ)+1)*(a-z) →
    (E : ℝ)*(b-z)≤b → b≤((E : ℝ)+1)*(b-z) → RP D a z M≤RP E b z M := by
  induction D with
  | zero => intro E a b z M hE hED;omega
  | succ D ih =>
    intro E a b z M hE hED hM ha hab hb hz hDa haD hEb hbE
    by_cases heq : E=D+1
    · subst E
      exact RP_mono_cell hE hM ha hab hb hz hDa hEb
    · have hED' : E≤D := by omega
      have hD : 2≤D := by omega
      have hDpos : (0 : ℝ)<D := by positivity
      have hz0 : 0≤z := by linarith only [hM,ha,hab,hb]
      have hbm : 0≤b-z := by linarith only [hM,hz,ha,hab]
      let c := ((D : ℝ)+1)*z/(D : ℝ)
      have hac : a≤c := by
        apply (le_div_iff₀ hDpos).mpr
        push_cast at hDa
        nlinarith only [hDa]
      have hcb : c≤b := by
        apply (div_le_iff₀ hDpos).mpr
        have hER : (E : ℝ)+1≤(D : ℝ)+1 := by exact_mod_cast Nat.succ_le_succ hED'
        have hh := mul_le_mul_of_nonneg_right hER hbm
        nlinarith only [hbE,hh]
      have hcphase : ((D : ℝ)+1)*(c-z)=c := by dsimp only [c];field_simp;ring
      have hcm : 0≤c-z := by
        have he : c-z=z/(D : ℝ) := by dsimp only [c];field_simp;ring
        rw [he]
        positivity
      have hrec := ih E c b z M hE hED' hM (ha.trans hac) hcb hb hz
        (by nlinarith only [hcphase,hcm] : (D : ℝ)*(c-z)≤c) hcphase.symm.le hEb hbE
      have htop := RP_mono_cell (by omega : 2≤D+1) hM ha hac (hcb.trans hb) hz hDa
        (by push_cast;exact hcphase.le)
      change RP (D+1) a z M≤RP (D+1) (((D : ℝ)+1)*z/(D : ℝ)) z M at htop
      rw [RP_boundary D (by omega : 1≤D)] at htop
      exact htop.trans hrec

theorem P_eq_RP_high {y z M : ℝ} (hM : 31≤M) (hy : M≤y) (hyz : y≤2*z) :
    P y z M=RP (Step y (y-z)) y z M := by
  have h1 : 0≤3*z-y-1 := by linarith only [hM,hy,hyz]
  have h2 : 0≤5*z-2*y-2 := by linarith only [hM,hy,hyz]
  have h3 : 0≤y-2-2*(7*M/25) := by linarith only [hM,hy]
  have h4 : 0≤y-3-3*(7*M/25) := by linarith only [hM,hy]
  unfold P RP QH Q
  rw [max_eq_left h1,max_eq_left h2,max_eq_left h3,max_eq_left h4,Jstar_eq_JP]
  ring

theorem P_high_mono {a b z M : ℝ} (hM : 31≤M) (ha : M≤a) (hab : a≤b)
    (hb : b≤2*z) (hz : z≤4*M/5) : P a z M≤P b z M := by
  have hz0 : 0≤z := by linarith only [hM,ha,hab,hb]
  have ha0 : 0<a := by linarith only [hM,ha]
  have hb0 : 0<b := lt_of_lt_of_le ha0 hab
  have ham : 0<a-z := by linarith only [hM,ha,hz]
  have hbm : 0<b-z := by linarith only [hM,ha,hab,hz]
  have hda := step_bounds ha0.le ham
  have hdb := step_bounds hb0.le hbm
  have hrat2 : (2 : ℝ)≤b/(b-z) := (le_div_iff₀ hbm).mpr (by linarith only [hb])
  have hE : 2≤Step b (b-z) := Nat.le_floor (by simpa only [Nat.cast_ofNat] using hrat2)
  have hrat : b/(b-z)≤a/(a-z) := by
    apply (div_le_div_iff₀ hbm ham).mpr
    nlinarith only [mul_nonneg hz0 (sub_nonneg.mpr hab)]
  have hED : Step b (b-z)≤Step a (a-z) := Nat.floor_mono hrat
  rw [P_eq_RP_high hM ha (hab.trans hb),P_eq_RP_high hM (ha.trans hab) hb]
  exact RP_cross _ _ a b z M hE hED hM ha hab hb hz hda.1 hda.2.le hdb.1 hdb.2.le

#print axioms RP_cross
#print axioms P_high_mono
end
end JSP233.UniformHigh208
