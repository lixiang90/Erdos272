module

public import Erdos272.Arithmetic.UniformLow208
public import Erdos272.Resources.UniformActual208

@[expose] public section

/-! Exact concavity on each of the three low-density neighbor pieces. -/
namespace JSP233.UniformConcave208
open UniformSourceCore208 UniformLow208 UniformActual208 NeighborMass208 Set
noncomputable section
set_option maxHeartbeats 0

def Branch (A B y z M : ℝ) : ℝ := z*(y-1-7*M/25)+
  A/2*(3*z-y-1)*(y-2-14*M/25)+B/3*(5*z-2*y-2)*(y-3-21*M/25)+160/M*LowJ y z
def C3 (M : ℝ) : ℝ := 160/M*(1-Delta*UniformSourceCore208.Sigma)/6
def C2 (A B M : ℝ) : ℝ := -A/2-2*B/3-22/M
def C1 (A B z M : ℝ) : ℝ := z+A/2*(3*z-1+(2+14*M/25))+
  B/3*(5*z-2+2*(3+21*M/25))+160/M*(Delta*z^2/2+Delta*z/2-2014/625)
def C0 (A B z M : ℝ) : ℝ := -z*(1+7*M/25)-A/2*(3*z-1)*(2+14*M/25)-
  B/3*(5*z-2)*(3+21*M/25)+160/M*(-Delta*z^3/3-Delta*z^2/2)

theorem branch_cubic {M : ℝ} (hM : M≠0) (A B y z : ℝ) :
    Branch A B y z M=Cubic (C3 M) (C2 A B M) (C1 A B z M) (C0 A B z M) y := by
  unfold Branch Cubic C3 C2 C1 C0 LowJ
  field_simp
  ring

theorem branch_min {A B a b x z M q : ℝ} (hM : 0<M) (hA : 0≤A) (hB : 0≤B)
    (ha : 0≤a) (hax : a≤x) (hxb : x≤b)
    (hqa : q≤Branch A B a z M) (hqb : q≤Branch A B b z M) : q≤Branch A B x z M := by
  have h3 : C3 M≤0 := by
    unfold C3
    exact div_nonpos_of_nonpos_of_nonneg
      (mul_nonpos_of_nonneg_of_nonpos (by positivity) (by norm_num [Delta,UniformSourceCore208.Sigma])) (by norm_num)
  have h2 : C2 A B M≤0 := by
    unfold C2
    have h22 : 0≤22/M := by positivity
    linarith only [hA,hB,h22]
  rw [branch_cubic (ne_of_gt hM)] at hqa hqb ⊢
  exact cubic_min ha hax hxb h3 h2 hqa hqb

theorem P_eq_branch {A B y z M : ℝ} (hM : 31≤M) (hy : M≤y) (hz : 0≤z) (hzy : 2*z≤y)
    (hA : max (3*z-y-1) 0=A*(3*z-y-1)) (hB : max (5*z-2*y-2) 0=B*(5*z-2*y-2)) :
    P y z M=Branch A B y z M := by
  have h3 : 0≤y-2-2*(7*M/25) := by linarith only [hM,hy]
  have h4 : 0≤y-3-3*(7*M/25) := by linarith only [hM,hy]
  unfold P Q Branch
  rw [hA,hB,max_eq_left h3,max_eq_left h4,Jstar_low (by linarith only [hM,hy]) hz hzy]
  ring

theorem P_min_branch {A B a b x z M q : ℝ} (hM : 31≤M) (hMa : M≤a) (hz : 0≤z)
    (hza : 2*z≤a) (hax : a≤x) (hxb : x≤b) (hA : 0≤A) (hB : 0≤B)
    (hAA : ∀ y∈Icc a b,max (3*z-y-1) 0=A*(3*z-y-1))
    (hBB : ∀ y∈Icc a b,max (5*z-2*y-2) 0=B*(5*z-2*y-2))
    (hqa : q≤P a z M) (hqb : q≤P b z M) : q≤P x z M := by
  have hab := hax.trans hxb
  rw [P_eq_branch hM hMa hz hza (hAA a ⟨le_rfl,hab⟩) (hBB a ⟨le_rfl,hab⟩)] at hqa
  rw [P_eq_branch hM (hMa.trans hab) hz (hza.trans hab) (hAA b ⟨hab,le_rfl⟩) (hBB b ⟨hab,le_rfl⟩)] at hqb
  rw [P_eq_branch hM (hMa.trans hax) hz (hza.trans hax) (hAA x ⟨hax,hxb⟩) (hBB x ⟨hax,hxb⟩)]
  exact branch_min (by linarith only [hM] : 0<M) hA hB (by linarith only [hM,hMa]) hax hxb hqa hqb

theorem P_min_11 {a b x z M q : ℝ} (hM : 31≤M) (hMa : M≤a) (hz : 0≤z)
    (hza : 2*z≤a) (hax : a≤x) (hxb : x≤b) (hb : b≤(5*z-2)/2)
    (hqa : q≤P a z M) (hqb : q≤P b z M) : q≤P x z M := by
  apply P_min_branch (A:=1) (B:=1) hM hMa hz hza hax hxb (by norm_num) (by norm_num) _ _ hqa hqb
  · intro y hy
    rw [max_eq_left (by linarith only [hy.2,hb,hz] : 0≤3*z-y-1),one_mul]
  · intro y hy
    rw [max_eq_left (by linarith only [hy.2,hb] : 0≤5*z-2*y-2),one_mul]

theorem P_min_10 {a b x z M q : ℝ} (hM : 31≤M) (hMa : M≤a) (hz : 0≤z)
    (hza : 2*z≤a) (hax : a≤x) (hxb : x≤b) (ha : (5*z-2)/2≤a) (hb : b≤3*z-1)
    (hqa : q≤P a z M) (hqb : q≤P b z M) : q≤P x z M := by
  apply P_min_branch (A:=1) (B:=0) hM hMa hz hza hax hxb (by norm_num) (by norm_num) _ _ hqa hqb
  · intro y hy
    rw [max_eq_left (by linarith only [hy.2,hb] : 0≤3*z-y-1),one_mul]
  · intro y hy
    rw [max_eq_right (by linarith only [hy.1,ha] : 5*z-2*y-2≤0),zero_mul]

theorem P_min_00 {a b x z M q : ℝ} (hM : 31≤M) (hMa : M≤a) (hz : 0≤z)
    (hza : 2*z≤a) (hax : a≤x) (hxb : x≤b) (ha : 3*z-1≤a)
    (hqa : q≤P a z M) (hqb : q≤P b z M) : q≤P x z M := by
  apply P_min_branch (A:=0) (B:=0) hM hMa hz hza hax hxb (by norm_num) (by norm_num) _ _ hqa hqb
  · intro y hy
    rw [max_eq_right (by linarith only [hy.1,ha] : 3*z-y-1≤0),zero_mul]
  · intro y hy
    rw [max_eq_right (by linarith only [hy.1,ha,hz] : 5*z-2*y-2≤0),zero_mul]

#print axioms branch_min
#print axioms P_min_11
#print axioms P_min_10
#print axioms P_min_00
end
end JSP233.UniformConcave208
