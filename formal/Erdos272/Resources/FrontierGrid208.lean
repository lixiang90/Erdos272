import Erdos272.Resources.LocalizedMiddle208
import Mathlib.Tactic

/-! The floor error of the actual localized frontier is paid at L/d. -/
namespace JSP233.FrontierGrid208
open LocalizedMiddle208
open scoped Classical BigOperators
noncomputable section
set_option maxHeartbeats 0

def Objective (rho C A t : ℝ) : ℝ := -C*A+(1-rho)*C*t-rho*t^2/2

theorem objective_le_main {rho C A t : ℝ} (hrho : 0 < rho) (ht : A ≤ t) :
    Objective rho C A t ≤ FrontierMain rho C A := by
  have hh := frontier_complete_square (rho := rho) (C := C) (A := A) (e := t)
    (a := 0) (err := 0)
    (P := rho*C*t+(61/200)*t) (U := rho*t^2/2-(61/200)*t)
    hrho (by norm_num) ht (by ring_nf; exact le_rfl) le_rfl
  dsimp only [Objective]
  norm_num only [zero_mul, zero_pow, zero_div, add_zero] at hh
  linarith only [hh]

theorem main_floor_error {rho C A C' A' : ℝ} (hrho : 0 < rho) (hrho1 : rho ≤ 1)
    (hC : 0 ≤ C) (hA : 0 ≤ A) (hCC : C ≤ C') (hAA : A ≤ A')
    (hCdiff : C' ≤ C+1) (hAdiff : A' ≤ A+1) :
    FrontierMain rho C A ≤ FrontierMain rho C' A' + 2*(C'+A') := by
  let v := max A ((1/rho-1)*C)
  let w := max A' v
  have hvA : A ≤ v := le_max_left _ _
  have hv0 : 0 ≤ v := hA.trans hvA
  have hC' : 0 ≤ C' := hC.trans hCC
  have hA' : 0 ≤ A' := hA.trans hAA
  have hCcost : A*(C'-C) ≤ A' := by
    have hh := mul_le_mul_of_nonneg_left (show C'-C ≤ 1 by linarith only [hCdiff]) hA
    nlinarith only [hh, hAA]
  have hAcost : C'*(A'-A) ≤ C' := by
    have hh := mul_le_mul_of_nonneg_left (show A'-A ≤ 1 by linarith only [hAdiff]) hC'
    simpa only [mul_one] using hh
  have hCgain : 0 ≤ (1-rho)*(C'-C)*v := by positivity
  have hfirst : Objective rho C A v ≤ Objective rho C' A' v + A' + C' := by
    dsimp only [Objective]
    nlinarith only [hCcost, hAcost, hCgain]
  have hsecond : Objective rho C' A' v ≤ Objective rho C' A' w + A' := by
    by_cases hAv : A' ≤ v
    · have hw : w = v := max_eq_right hAv
      rw [hw]
      linarith only [hA']
    · have hw : w = A' := max_eq_left (le_of_not_ge hAv)
      have hvhi : v ≤ A' := le_of_not_ge hAv
      have hdiff : A'-v ≤ 1 := by linarith only [hAdiff, hvA]
      have hpos : 0 ≤ A'-v := sub_nonneg.mpr hvhi
      have hsum : rho*(A'+v)/2 ≤ A' := by
        have hh := mul_le_of_le_one_left (show 0 ≤ A'+v by positivity) hrho1
        linarith only [hh, hvhi]
      have hneg : 0 ≤ (1-rho)*C' := by positivity
      have hcost := mul_le_mul_of_nonneg_left (show rho*(A'+v)/2-(1-rho)*C' ≤ A' by
        linarith only [hsum,hneg]) hpos
      have hcap := mul_le_mul_of_nonneg_right hdiff hA'
      rw [hw]
      dsimp only [Objective]
      nlinarith only [hcost,hcap]
  have hthird := objective_le_main (C := C') hrho (show A' ≤ w from le_max_left _ _)
  have hmain : FrontierMain rho C A = Objective rho C A v := rfl
  rw [hmain]
  linarith only [hfirst,hsecond,hthird,hC']

theorem main_div_scale {rho C A d : ℝ} (hd : 0 < d) :
    FrontierMain rho (C/d) (A/d) = FrontierMain rho C A / d^2 := by
  have hmax : max (A/d) ((1/rho-1)*(C/d)) = max A ((1/rho-1)*C) / d := by
    rw [← mul_div_assoc]
    simpa only [div_eq_mul_inv] using
      (max_mul_of_nonneg A ((1/rho-1)*C) (inv_nonneg.mpr hd.le)).symm
  dsimp only [FrontierMain]
  rw [hmax]
  ring

theorem main_floor_physical {rho : ℝ} {c L d : ℕ}
    (hrho : 0 < rho) (hrho1 : rho ≤ 1) (hcL : c ≤ L) (hd : 0 < d) :
    FrontierMain rho (c/d : ℕ) ((L-c)/d : ℕ) ≤
      FrontierMain rho c ((L : ℝ)-c) / (d : ℝ)^2 + 2*(L : ℝ)/d := by
  have hC := TotientFloor29.nat_div_bounds c d hd
  have hA := TotientFloor29.nat_div_bounds (L-c) d hd
  rw [Nat.cast_sub hcL] at hA
  have hh := main_floor_error hrho hrho1 (Nat.cast_nonneg (c/d))
    (Nat.cast_nonneg ((L-c)/d)) hC.1 hA.1 hC.2 hA.2
  rw [main_div_scale (by exact_mod_cast hd)] at hh
  have heq : 2*((c : ℝ)/d+((L : ℝ)-c)/d)=2*(L : ℝ)/d := by ring
  rwa [heq] at hh

theorem anchor_le_sum {rho C A : ℝ} (hrho : 1/2 ≤ rho) (hC : 0 ≤ C) (hA : 0 ≤ A) :
    max A ((1/rho-1)*C) ≤ C+A := by
  have hrho0 : 0 < rho := by linarith only [hrho]
  have hratio : 1/rho-1 ≤ 1 := by
    apply (sub_le_iff_le_add).mpr
    apply (div_le_iff₀ hrho0).mpr
    linarith only [hrho]
  apply max_le
  · linarith only [hC]
  · have hh := mul_le_mul_of_nonneg_right hratio hC
    linarith only [hh,hA]

theorem anchor_physical {rho : ℝ} {c L d : ℕ}
    (hrho : 1/2 ≤ rho) (hcL : c ≤ L) :
    max (((L-c)/d : ℕ) : ℝ) ((1/rho-1)*(c/d : ℕ)) ≤ (L : ℝ)/d := by
  have hh := anchor_le_sum hrho (Nat.cast_nonneg (c/d)) (Nat.cast_nonneg ((L-c)/d))
  have hC := Nat.cast_div_le (α := ℝ) (m := c) (n := d)
  have hA := Nat.cast_div_le (α := ℝ) (m := L-c) (n := d)
  rw [Nat.cast_sub hcL] at hA
  have heq : (c : ℝ)/d+((L : ℝ)-c)/d=(L : ℝ)/d := by ring
  linarith only [hh,hC,hA,heq]

theorem main_density_deficit {rho C A : ℝ} (hrho : 200/329 ≤ rho)
    (hrho1 : rho ≤ 1) (hC : 0 ≤ C) (hA : 0 ≤ A) :
    FrontierMain rho C A / rho - C^2/2 ≤ -(23359/80000 : ℝ)*(C+A)^2 := by
  have hrho0 : 0 < rho := by linarith only [hrho]
  let alpha : ℝ := 129/200
  let v := max A ((1/rho-1)*C)
  have hCAsq : 0 ≤ C*A := mul_nonneg hC hA
  have hratio : 1/rho-1 ≤ alpha := by
    apply (sub_le_iff_le_add).mpr
    apply (div_le_iff₀ hrho0).mpr
    dsimp only [alpha]
    nlinarith only [hrho]
  by_cases hAv : A ≤ (1/rho-1)*C
  · have hvEq : v = (1/rho-1)*C := max_eq_right hAv
    have hcenter : rho*v=(1-rho)*C := by rw [hvEq]; field_simp <;> ring
    have hv0 : 0 ≤ v := hA.trans (le_max_left _ _)
    have hvhi : v ≤ alpha*C := by rw [hvEq]; exact mul_le_mul_of_nonneg_right hratio hC
    have hAhi : A ≤ alpha*C := (le_max_left _ _).trans hvhi
    have hv2 : v^2 ≤ alpha^2*C^2 := by
      have hh := (sq_le_sq₀ hv0 (mul_nonneg (by norm_num [alpha]) hC)).mpr hvhi
      nlinarith only [hh]
    have hCAfrac : C*A ≤ C*A/rho := (le_div_iff₀ hrho0).mpr
      (mul_le_of_le_one_right hCAsq hrho1)
    have hacross := mul_le_mul_of_nonneg_right hAhi hA
    have hmain : FrontierMain rho C A / rho = -C*A/rho+v^2/2 := by
      dsimp only [FrontierMain]
      change (-C*A+(1-rho)*C*v-rho*v^2/2)/rho = _
      field_simp
      nlinarith only [congrArg (fun x : ℝ => x*v) hcenter]
    rw [hmain]
    dsimp only [alpha] at hv2 hacross
    have hvhalf : v^2/2-C^2/2 ≤ -(23359/80000 : ℝ)*C^2 := by nlinarith only [hv2]
    have hcross : -C*A/rho ≤ -(C*A) := by
      rw [neg_mul, neg_div]
      exact neg_le_neg hCAfrac
    have hresult : -(C*A)+(-(23359/80000 : ℝ)*C^2) ≤ -(23359/80000 : ℝ)*(C+A)^2 := by
      nlinarith only [hacross,hCAsq]
    calc
      -C*A/rho+v^2/2-C^2/2 = -C*A/rho+(v^2/2-C^2/2) := by ring
      _ ≤ -(C*A)+(-(23359/80000 : ℝ)*C^2) := add_le_add hcross hvhalf
      _ ≤ _ := hresult
  · have hvEq : v = A := max_eq_left (le_of_not_ge hAv)
    have hmain : FrontierMain rho C A / rho = -C*A-A^2/2 := by
      dsimp only [FrontierMain]
      change (-C*A+(1-rho)*C*v-rho*v^2/2)/rho = _
      rw [hvEq]
      field_simp
      ring
    rw [hmain]
    nlinarith only [sq_nonneg (C+A)]

theorem main_lower {rho C A : ℝ} (hrho : 0 < rho) (hrho1 : rho ≤ 1)
    (hC : 0 ≤ C) (hA : 0 ≤ A) :
    -(C+A)^2/2 ≤ FrontierMain rho C A := by
  have hm := objective_le_main (C := C) hrho (le_refl A)
  have hCA := mul_le_of_le_one_left (mul_nonneg hC hA) hrho1
  have hAA := mul_le_of_le_one_left (sq_nonneg A) hrho1
  dsimp only [Objective] at hm
  nlinarith only [hm,hCA,hAA,sq_nonneg C]

theorem truncated_main_tail {rho C A L Z : ℝ} (hrho : 0 < rho) (hrho1 : rho ≤ 1)
    (hC : 0 ≤ C) (hA : 0 ≤ A) (hL : 0 < L) (hCA : C+A=L)
    (hZ : Z ≤ 1/rho) (hTail : 1/rho-Z ≤ 1/L) :
    FrontierMain rho C A * Z ≤ FrontierMain rho C A / rho + L/2 := by
  let g := FrontierMain rho C A
  by_cases hg : 0 ≤ g
  · have hh := mul_le_mul_of_nonneg_left hZ hg
    change g*Z ≤ g/rho+L/2
    have hL0 : 0 ≤ L/2 := by positivity
    rw [mul_one_div] at hh
    linarith only [hh,hL0]
  · have hl := main_lower hrho hrho1 hC hA
    rw [hCA] at hl
    have hh := mul_le_mul (show -g ≤ L^2/2 by dsimp only [g]; linarith only [hl]) hTail
      (sub_nonneg.mpr hZ) (by positivity : (0 : ℝ) ≤ L^2/2)
    have heq : L^2/2*(1/L)=L/2 := by field_simp
    rw [heq] at hh
    change g*Z ≤ g/rho+L/2
    have heqg : -g*(1/rho-Z)=g*Z-g/rho := by ring
    rw [heqg] at hh
    linarith only [hh]

#print axioms objective_le_main
#print axioms main_floor_error
#print axioms main_floor_physical
#print axioms anchor_physical
#print axioms main_density_deficit
#print axioms truncated_main_tail
end
end JSP233.FrontierGrid208
