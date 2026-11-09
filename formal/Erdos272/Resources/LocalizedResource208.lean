module

public import Erdos272.Resources.GcdResource208
public import Erdos272.Resources.FrontierGrid208
public import Erdos272.Resources.FrontierSum208
public import Erdos272.Resources.RawEndpoint115
public import Mathlib.Algebra.BigOperators.Ring.Finset
public import Mathlib.Order.Interval.Finset.Nat

@[expose] public section

/-! The actual middle resource is summed before the local error is estimated.
The totient and finite reciprocal-square estimates are explicit hypotheses here. -/
namespace JSP233.LocalizedResource208
open CoprimeDensity52 MiddleJoint51 ResourceSymmetry56 LocalizedMiddle208
open FrontierGrid208 FrontierSum208 GcdResource208
open scoped Classical BigOperators
noncomputable section
set_option maxHeartbeats 0

theorem resource_zero_left {A M e : ℕ} (hAe : A ≤ e) (heM : e ≤ M) :
    (ResourceCount 0 A M e : ℝ) ≤ (UpperTriangle 0 M).card := by
  rw [resource_frontier_identity hAe heM]
  have hU : (0 : ℝ) ≤ TotientTriangle e := Nat.cast_nonneg _
  have hzero : ∀ t, coprimeRectangle 0 t = ∅ := by
    intro t
    ext p
    simp only [Finset.notMem_empty, iff_false, mem_rectangle]
    omega
  simp only [hzero, Finset.card_empty, Nat.cast_zero, zero_add, zero_mul, sub_zero, add_zero]
  rw [actual_triangle_totient]
  linarith only [hU]

theorem resource_physical_local {rho : ℝ} {N c L R d e : ℕ}
    (hrho : 200/329 ≤ rho) (hrho1 : rho ≤ 1)
    (hcL : c ≤ L) (hLR : L ≤ R) (hRN : R ≤ N)
    (hd : d ∈ Finset.Icc 1 L) (hAe : (L-c)/d ≤ e) (heM : e ≤ (R-c)/d)
    (hF : rho * (c/d : ℕ) - 17/200 ≤ TotientRows208.TotientMass (c/d))
    (hU : rho * (e : ℝ)^2/2 - (61/200)*e ≤ TotientTriangle e) :
    (ResourceCount (c/d) ((L-c)/d) ((R-c)/d) e : ℝ) ≤
      (coprimeRectangle (c/d) ((R-c)/d)).card +
      (UpperTriangle 0 ((R-c)/d)).card +
      FrontierMain rho c ((L : ℝ)-c)/(d : ℝ)^2 + Error L d := by
  have hrho0 : 0 < rho := by linarith only [hrho]
  have hdpos := (Finset.mem_Icc.mp hd).1
  have hmain := main_floor_physical hrho0 hrho1 hcL hdpos
  have hanchor := anchor_physical (rho := rho) (by linarith only [hrho]) hcL (d := d)
  have hrow := row_error_physical hcL hd
  have hrecip : 1/rho ≤ (329/200 : ℝ) := by
    apply (div_le_iff₀ hrho0).mpr
    linarith only [hrho]
  have hq := mul_le_mul_of_nonneg_right hrecip (by norm_num : (0 : ℝ) ≤ (39/100)^2/2)
  have hh := actual_resource_frontier_bound hrho0 hAe heM hF hU
  rw [← actual_triangle_totient] at hh
  have ha := mul_le_mul_of_nonneg_left hanchor (by norm_num : (0 : ℝ) ≤ 39/100)
  dsimp only [Error]
  have hq' : (39/100 : ℝ)^2/(2*rho) ≤ (329/200 : ℝ)*(39/100)^2/2 := by
    calc
      (39/100 : ℝ)^2/(2*rho) = (1/rho)*((39/100)^2/2) := by ring
      _ ≤ _ := hq
      _ = _ := by ring
  calc
    _ ≤ (coprimeRectangle (c/d) ((R-c)/d)).card +
        (UpperTriangle 0 ((R-c)/d)).card +
        (FrontierMain rho c ((L : ℝ)-c)/(d : ℝ)^2+2*(L : ℝ)/d) +
        (39/100 : ℝ)*((L : ℝ)/d) + (329/200 : ℝ)*(39/100)^2/2 +
        ((L : ℝ)/(2*d))*Real.log ((L : ℝ)/d) := by
      linarith only [hh,hmain,ha,hrow,hq']
    _ = _ := by ring

theorem actual_resource_sum_local {rho : ℝ} {N c L R : ℕ}
    (hrho : 200/329 ≤ rho) (hrho1 : rho ≤ 1)
    (hL : 1 ≤ L) (hcL : c ≤ L) (hLR : L ≤ R) (hRN : R ≤ N)
    (e : ℕ → ℕ) (he : ∀ d ∈ Finset.Icc 1 N, (L-c)/d ≤ e d ∧ e d ≤ (R-c)/d)
    (hF : ∀ t ≤ N, rho * t - 17/200 ≤ TotientRows208.TotientMass t)
    (hU : ∀ t ≤ N, rho * (t : ℝ)^2/2 - (61/200)*t ≤ TotientTriangle t)
    (hZ : reciprocalSquareSum L ≤ 1/rho)
    (hTail : 1/rho-reciprocalSquareSum L ≤ 1/(L : ℝ)) :
    ((∑ d ∈ Finset.Icc 1 N,
      ResourceCount (c/d) ((L-c)/d) ((R-c)/d) (e d) : ℕ) : ℝ) ≤
      (R : ℝ)^2/2 - (23359/80000 : ℝ)*L^2 +
      (L : ℝ)*Polynomial (Real.log L) := by
  let base := fun d : ℕ => ((coprimeRectangle (c/d) ((R-c)/d)).card : ℝ) +
    (UpperTriangle 0 ((R-c)/d)).card
  let fee := fun d : ℕ => FrontierMain rho c ((L : ℝ)-c)/(d : ℝ)^2 + Error L d
  have hLN : L ≤ N := hLR.trans hRN
  have hterms : ∀ d ∈ Finset.Icc 1 N,
      (ResourceCount (c/d) ((L-c)/d) ((R-c)/d) (e d) : ℝ) ≤
      base d + (if d ≤ L then fee d else 0) := by
    intro d hd
    by_cases hdL : d ≤ L
    · rw [if_pos hdL]
      have hh := resource_physical_local hrho hrho1 hcL hLR hRN
        (Finset.mem_Icc.mpr ⟨(Finset.mem_Icc.mp hd).1, hdL⟩)
        (he d hd).1 (he d hd).2
        (hF (c/d) ((Nat.div_le_self _ _).trans (hcL.trans hLN)))
        (hU (e d) ((he d hd).2.trans ((Nat.div_le_self _ _).trans
          ((Nat.sub_le R c).trans hRN))))
      dsimp only [base,fee]
      linarith only [hh]
    · rw [if_neg hdL, add_zero]
      have hc0 : c/d=0 := Nat.div_eq_of_lt (by omega)
      rw [hc0]
      have hh := resource_zero_left (he d hd).1 (he d hd).2
      dsimp only [base]
      rw [hc0]
      have hzero : coprimeRectangle 0 ((R-c)/d) = ∅ := by
        ext p
        simp only [Finset.notMem_empty, iff_false, mem_rectangle]
        omega
      simpa only [hzero, Finset.card_empty, Nat.cast_zero, zero_add] using hh
  have hs := Finset.sum_le_sum hterms
  have hcut : (∑ d ∈ Finset.Icc 1 N, if d ≤ L then fee d else 0) =
      ∑ d ∈ Finset.Icc 1 L, fee d := by
    rw [← Finset.sum_filter]
    congr 1
    ext d
    simp only [Finset.mem_filter, Finset.mem_Icc]
    omega
  have hbase : (∑ d ∈ Finset.Icc 1 N, base d) =
      (R : ℝ)^2/2-(c : ℝ)^2/2-((R : ℝ)-c)/2 := by
    simpa only [base, Nat.cast_sum, Nat.cast_add] using
      physical_base_identity (hcL.trans hLR) hRN
  rw [Finset.sum_add_distrib,hcut,hbase] at hs
  have hlocal : (∑ d ∈ Finset.Icc 1 L, fee d) =
      FrontierMain rho c ((L : ℝ)-c)*reciprocalSquareSum L +
      ∑ d ∈ Finset.Icc 1 L, Error L d := by
    simp only [fee, Finset.sum_add_distrib, div_eq_mul_inv, ← Finset.mul_sum,
      reciprocalSquareSum]
  rw [hlocal] at hs
  have hCA : (c : ℝ)+((L : ℝ)-c)=L := by ring
  have hA : (0 : ℝ) ≤ (L : ℝ)-c := sub_nonneg.mpr (by exact_mod_cast hcL)
  have hrho0 : 0 < rho := by linarith only [hrho]
  have htail := truncated_main_tail hrho0 hrho1 (Nat.cast_nonneg c) hA
    (by exact_mod_cast (show 0<L by omega)) hCA hZ hTail
  have hdef := main_density_deficit hrho hrho1 (Nat.cast_nonneg c) hA
  rw [hCA] at hdef
  have herr := complete_error_bound hL
  have hRc : (0 : ℝ) ≤ (R : ℝ)-c := sub_nonneg.mpr
    (by exact_mod_cast (hcL.trans hLR))
  push_cast
  linarith only [hs,htail,hdef,herr,hRc]

theorem actual_middle_profile_local {rho : ℝ} {N c L R : ℕ}
    (hrho : 200/329 ≤ rho) (hrho1 : rho ≤ 1)
    (hL : 1 ≤ L) (hcL : c ≤ L) (hLR : L ≤ R) (hRN : R ≤ N)
    (e : ℕ → ℕ) (he : ∀ d ∈ Finset.Icc 1 N, (L-c)/d ≤ e d ∧ e d ≤ (R-c)/d)
    (hF : ∀ t ≤ N, rho * t - 17/200 ≤ TotientRows208.TotientMass t)
    (hU : ∀ t ≤ N, rho * (t : ℝ)^2/2 - (61/200)*t ≤ TotientTriangle t)
    (hZ : reciprocalSquareSum L ≤ 1/rho)
    (hTail : 1/rho-reciprocalSquareSum L ≤ 1/(L : ℝ)) :
    ((R : ℝ)+(129/200)*L)*(N-R) +
      ((∑ d ∈ Finset.Icc 1 N,
        ResourceCount (c/d) ((L-c)/d) ((R-c)/d) (e d) : ℕ) : ℝ) ≤
      (N : ℝ)^2/2-RawEndpoint115.ProfileDeficit L (N-R) +
      (L : ℝ)*Polynomial (Real.log L) := by
  have hh := actual_resource_sum_local hrho hrho1 hL hcL hLR hRN e he hF hU hZ hTail
  dsimp only [RawEndpoint115.ProfileDeficit]
  nlinarith only [hh]

#print axioms resource_zero_left
#print axioms resource_physical_local
#print axioms actual_resource_sum_local
#print axioms actual_middle_profile_local
end
end JSP233.LocalizedResource208
