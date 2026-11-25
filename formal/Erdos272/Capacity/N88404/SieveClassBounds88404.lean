module

public import Erdos272.Counting.N88404.APClassFrame88404
public import Erdos272.Capacity.N88404.SieveConstants88404
public import Erdos272.Arithmetic.N291012.ShadowResponse291012

@[expose] public section

namespace JSP233.SieveClassBounds88404
open StarCompletion APGeometry APShadowCapacity16858 APClasses88404 APClassFrame88404
open SieveConstants88404
open scoped Classical BigOperators
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2000000

theorem actual_geometry {N d : ℕ} {F : Finset (Finset ℤ)}
    (hN : 1 ≤ N) (hd : 0 < d) (hF : Legal (Ground N) F) :
    ∃ w y : ℝ, 0 ≤ w ∧ (d : ℝ)*w ≤ (N : ℝ)-1 ∧ 0 ≤ y ∧ 2*y ≤ w ∧
      ((StepAP F d).card : ℝ) ≤ y^2+w ∧
      8*y^3 ≤ 6*((APShadow (StepAP F d)).card : ℝ)+w := by
  obtain ⟨f⟩ := frame_nonempty hN hd hF
  obtain ⟨y, hy, hyw, hc, hs⟩ := geometry f hd
  refine ⟨(f.size : ℝ)-1, y, ?_, f.span, hy, hyw, hc, hs⟩
  have hh : (1 : ℝ) ≤ f.size := by exact_mod_cast f.size_positive
  linarith only [hh]

theorem unit_bound {N : ℕ} {F : Finset (Finset ℤ)} {g : ℝ}
    (hN : 1 ≤ N) (hg : 0 < g) (hF : Legal (Ground N) F) :
    ((StepAP F 1).card : ℝ)-6*g*Alpha 1*((APShadow (StepAP F 1)).card : ℝ) ≤
      (1+g)*((N : ℝ)-1)+1/(432*(g*Alpha 1)^2) := by
  obtain ⟨w, y, hw, hspan, hy, hyw, hc, hs⟩ := actual_geometry hN (by decide : 0 < 1) hF
  have ha := alpha_range (p := 1) (by simp [Steps])
  have hwn : w ≤ (N : ℝ)-1 := by simpa only [Nat.cast_one, one_mul] using hspan
  have hm := mul_le_mul_of_nonneg_left hs (mul_nonneg hg.le ha.1.le)
  have hmax := ShadowResponse291012.cubic_max hy (mul_pos hg ha.1)
  have hw₁ := mul_le_mul_of_nonneg_right ha.2 (mul_nonneg hg.le hw)
  have hw₂ := mul_le_mul_of_nonneg_left hwn (show 0 ≤ 1+g by linarith only [hg])
  nlinarith only [hc, hm, hmax, hw₁, hw₂]

theorem selected_bound {N p : ℕ} {F : Finset (Finset ℤ)} {g : ℝ}
    (hN : 1 ≤ N) (hp : p ∈ Selected) (hg : 0 < g)
    (hcap : 3*g*((N : ℝ)-1) ≤ 1) (hF : Legal (Ground N) F) :
    ((StepAP F p).card : ℝ)-6*g*Alpha p*((APShadow (StepAP F p)).card : ℝ) ≤
      (1+g)*((N : ℝ)-1)/(p : ℝ)+((N : ℝ)-1)^2/(4*(p : ℝ)^2)-
        g*Alpha p*((N : ℝ)-1)^3/(p : ℝ)^3 := by
  have hpS : p ∈ Steps := Finset.mem_insert_of_mem hp
  have hpNat := (selected_range hp).1
  have hpR : (2 : ℝ) ≤ p := by exact_mod_cast hpNat
  have hp0 : (0 : ℝ) < p := by linarith only [hpR]
  have ha := alpha_range hpS
  obtain ⟨w, y, hw, hspan, hy, hyw, hc, hs⟩ := actual_geometry hN (steps_positive hpS) hF
  let n : ℝ := (N : ℝ)-1
  have hn : 0 ≤ n := by
    have hh : (1 : ℝ) ≤ N := by exact_mod_cast hN
    dsimp only [n]
    linarith only [hh]
  change (p : ℝ)*w ≤ n at hspan
  have hwn : w ≤ n/(p : ℝ) := (le_div_iff₀ hp0).mpr (by nlinarith only [hspan])
  have hyp := mul_le_mul_of_nonneg_left hyw hp0.le
  have hyb : y ≤ n/(2*(p : ℝ)) := (le_div_iff₀ (by positivity)).mpr
    (by nlinarith only [hyp, hspan])
  have hgan := mul_le_mul_of_nonneg_right ha.2 (mul_nonneg hg.le hn)
  have hbound : 12*g*Alpha p*n ≤ 2*(p : ℝ) := by
    change 3*g*n ≤ 1 at hcap
    nlinarith only [hcap, hgan, hpR]
  have hab : 12*(g*Alpha p)*(n/(2*(p : ℝ))) ≤ 1 := by
    have he : 12*(g*Alpha p)*(n/(2*(p : ℝ))) = (12*g*Alpha p*n)/(2*(p : ℝ)) := by ring
    rw [he]
    exact (div_le_one (by positivity)).mpr hbound
  have hmax := SieveScalars88404.endpoint_cubic (mul_nonneg hg.le ha.1.le) hy hyb hab
  have hend : (n/(2*(p : ℝ)))^2-8*(g*Alpha p)*(n/(2*(p : ℝ)))^3 =
      n^2/(4*(p : ℝ)^2)-g*Alpha p*n^3/(p : ℝ)^3 := by
    field_simp [hp0.ne']
    <;> ring
  rw [hend] at hmax
  have hm := mul_le_mul_of_nonneg_left hs (mul_nonneg hg.le ha.1.le)
  have hw₁ := mul_le_mul_of_nonneg_right ha.2 (mul_nonneg hg.le hw)
  have hw₂ := mul_le_mul_of_nonneg_left hwn (show 0 ≤ 1+g by linarith only [hg])
  have he : (1+g)*(n/(p : ℝ)) = (1+g)*n/(p : ℝ) := by ring
  rw [he] at hw₂
  change _ ≤ (1+g)*n/(p : ℝ)+n^2/(4*(p : ℝ)^2)-g*Alpha p*n^3/(p : ℝ)^3
  nlinarith only [hc, hm, hmax, hw₁, hw₂]

theorem selected_sum {N : ℕ} {F : Finset (Finset ℤ)} {g : ℝ}
    (hN : 1 ≤ N) (hg : 0 < g) (hcap : 3*g*((N : ℝ)-1) ≤ 1) (hF : Legal (Ground N) F) :
    let n := (N : ℝ)-1
    (∑ p ∈ Selected, ((StepAP F p).card : ℝ)) -
        6*g*(∑ p ∈ Selected, Alpha p*((APShadow (StepAP F p)).card : ℝ)) ≤
      (1+g)*n*(∑ p ∈ Selected, (1 : ℝ)/(p : ℝ)) +
        n^2*(∑ p ∈ Selected, (1 : ℝ)/(4*(p : ℝ)^2)) - g*n^3*(1-Alpha 1) := by
  let n : ℝ := (N : ℝ)-1
  let R : ℝ := ∑ p ∈ Selected, (1 : ℝ)/(p : ℝ)
  let Q : ℝ := ∑ p ∈ Selected, (1 : ℝ)/(4*(p : ℝ)^2)
  let c := fun p => ((StepAP F p).card : ℝ)
  let s := fun p => ((APShadow (StepAP F p)).card : ℝ)
  change (∑ p ∈ Selected, c p)-6*g*(∑ p ∈ Selected, Alpha p*s p) ≤
    (1+g)*n*R+n^2*Q-g*n^3*(1-Alpha 1)
  calc
    _ = ∑ p ∈ Selected, (c p-6*g*Alpha p*s p) := by
      rw [Finset.sum_sub_distrib, Finset.mul_sum]
      congr 1
      exact Finset.sum_congr rfl (fun p _ => by ring)
    _ ≤ ∑ p ∈ Selected, ((1+g)*n/(p : ℝ)+n^2/(4*(p : ℝ)^2)-
        g*Alpha p*n^3/(p : ℝ)^3) := by
      exact Finset.sum_le_sum (fun p hp => selected_bound hN hp hg hcap hF)
    _ = _ := by
      have he : ∀ p : ℕ, (1+g)*n/(p : ℝ)+n^2/(4*(p : ℝ)^2)-
          g*Alpha p*n^3/(p : ℝ)^3 =
          (1+g)*n*(1/(p : ℝ))+n^2*(1/(4*(p : ℝ)^2))-
            g*n^3*(Alpha p/(p : ℝ)^3) := by intro p; ring
      simp_rw [he]
      rw [Finset.sum_sub_distrib, Finset.sum_add_distrib,
        ← Finset.mul_sum, ← Finset.mul_sum, ← Finset.mul_sum, alpha_cube_sum]

#print axioms actual_geometry
#print axioms unit_bound
#print axioms selected_bound
end
end JSP233.SieveClassBounds88404
