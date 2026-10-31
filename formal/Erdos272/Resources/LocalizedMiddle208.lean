import Erdos272.Resources.ResourceSymmetry56
import Erdos272.Resources.TotientRows208
import Mathlib.Tactic

/-! Exact finite identities for the localized middle resource.
The frontier height remains the actual height selected by MiddleJoint51.
No finite totient estimate is assumed as a definition or axiom. -/
namespace JSP233.LocalizedMiddle208
open MiddleJoint51 CoprimeDensity52 ResourceSymmetry56
open scoped Classical BigOperators
noncomputable section
set_option maxHeartbeats 0

def TotientMass (t : ℕ) : ℝ := ∑ n ∈ Finset.Icc 1 t, (Nat.totient n : ℝ) / n
def TotientTriangle (t : ℕ) : ℕ := ∑ n ∈ Finset.Icc 2 t, Nat.totient n

theorem actual_triangle_totient (t : ℕ) :
    (UpperTriangle 0 t).card = TotientTriangle t := by
  have hm : Set.MapsTo (Prod.snd : ℕ × ℕ → ℕ)
      (↑(UpperTriangle 0 t) : Set (ℕ × ℕ)) (↑(Finset.Icc 2 t) : Set ℕ) := by
    intro p hp
    obtain ⟨ha, _, _, hb, _, hab⟩ := mem_triangle.mp hp
    exact Finset.mem_Icc.mpr ⟨by omega, hb⟩
  have hc := Finset.card_eq_sum_card_fiberwise hm
  rw [TotientTriangle]
  apply hc.trans
  apply Finset.sum_congr rfl
  intro b hb
  obtain ⟨hb2, hbt⟩ := Finset.mem_Icc.mp hb
  let I := (Finset.range b).filter (b.Coprime ·)
  have heq : (UpperTriangle 0 t).filter (fun p => p.2 = b) =
      I.image (fun a => (a, b)) := by
    ext p
    constructor
    · intro hp
      obtain ⟨hp, hpb⟩ := Finset.mem_filter.mp hp
      obtain ⟨ha, hat, _, hbt', hcop, hab⟩ := mem_triangle.mp hp
      apply Finset.mem_image.mpr
      refine ⟨p.1, Finset.mem_filter.mpr ⟨Finset.mem_range.mpr (by omega), ?_⟩, ?_⟩
      · simpa only [hpb] using hcop.symm
      · exact Prod.ext rfl hpb.symm
    · intro hp
      obtain ⟨a, ha, rfl⟩ := Finset.mem_image.mp hp
      obtain ⟨hab, hcop⟩ := Finset.mem_filter.mp ha
      have hab' := Finset.mem_range.mp hab
      have hapos : 0 < a := by
        by_contra h
        have ha0 : a = 0 := by omega
        have hb1 : b = 1 := by simpa only [ha0, Nat.coprime_zero_right] using hcop
        omega
      exact Finset.mem_filter.mpr ⟨mem_triangle.mpr
        ⟨hapos, by omega, by omega, hbt, hcop.symm, hab'⟩, rfl⟩
  rw [heq, Finset.card_image_of_injective _ (by
    intro a b h
    exact congrArg Prod.fst h)]
  rfl

theorem rectangle_cut_identity {C e M : ℕ} (heM : e ≤ M) :
    (CoprimeBox 0 C e M).card + (coprimeRectangle C e).card =
      (coprimeRectangle C M).card := by
  have hlo : (coprimeRectangle C M).filter (fun p => p.2 ≤ e) =
      coprimeRectangle C e := by
    ext p
    simp only [Finset.mem_filter, mem_rectangle]
    omega
  have hhi : (coprimeRectangle C M).filter (fun p => ¬ p.2 ≤ e) =
      CoprimeBox 0 C e M := by
    ext p
    simp only [Finset.mem_filter, mem_rectangle, mem_box]
    omega
  have hc := Finset.card_filter_add_card_filter_not (s := coprimeRectangle C M)
    (fun p => p.2 ≤ e)
  rw [hlo, hhi] at hc
  omega

theorem resource_frontier_identity {C A M e : ℕ} (hAe : A ≤ e) (heM : e ≤ M) :
    (ResourceCount C A M e : ℝ) =
      (coprimeRectangle C M).card + (TotientTriangle M : ℝ) +
      (C : ℝ) * e - C * A - (coprimeRectangle C e).card - TotientTriangle e := by
  have hr := rectangle_cut_identity (C := C) heM
  have ht := actual_upper_split heM
  have hn : ResourceCount C A M e + (coprimeRectangle C e).card +
      (UpperTriangle 0 e).card =
      C * (e - A) + (coprimeRectangle C M).card + (UpperTriangle 0 M).card := by
    dsimp only [ResourceCount]
    omega
  rw [actual_triangle_totient, actual_triangle_totient] at hn
  have hR : (ResourceCount C A M e : ℝ) + (coprimeRectangle C e).card +
      (TotientTriangle e : ℝ) =
      (C : ℝ) * ((e : ℝ) - A) + (coprimeRectangle C M).card + TotientTriangle M := by
    exact_mod_cast hn
  linarith only [hR]

def FrontierMain (rho C A : ℝ) : ℝ :=
  let v := max A ((1 / rho - 1) * C);
  -C * A + (1 - rho) * C * v - rho * v^2 / 2

theorem frontier_complete_square {rho C A e a err P U : ℝ}
    (hrho : 0 < rho) (ha : 0 ≤ a) (he : A ≤ e)
    (hP : rho * C * e - (a - 61 / 200) * e - err ≤ P)
    (hU : rho * e^2 / 2 - (61 / 200) * e ≤ U) :
    C * e - C * A - P - U ≤
      FrontierMain rho C A + a * max A ((1 / rho - 1) * C) + a^2 / (2 * rho) + err := by
  let v := max A ((1 / rho - 1) * C)
  have hAv : A ≤ v := le_max_left _ _
  have hv : (1 / rho - 1) * C ≤ v := le_max_right _ _
  have hcoef : (1-rho)*C ≤ rho*v := by
    have hm := mul_le_mul_of_nonneg_left hv hrho.le
    have heq : rho*((1/rho-1)*C)=(1-rho)*C := by field_simp <;> ring
    rwa [heq] at hm
  have hproj : 0 ≤ (e-v)*(rho*v-(1-rho)*C) := by
    by_cases hAe : A ≤ (1 / rho - 1) * C
    · have hvEq : v = (1 / rho - 1) * C := max_eq_right hAe
      have hcenter : rho * v = (1-rho)*C := by rw [hvEq]; field_simp <;> ring
      rw [hcenter, sub_self, mul_zero]
    · have hvEq : v = A := max_eq_left (le_of_not_ge hAe)
      exact mul_nonneg (sub_nonneg.mpr (by simpa only [hvEq] using he))
        (sub_nonneg.mpr hcoef)
  have hq : -C*A + (1-rho)*C*e-rho*e^2/2 + a*e ≤
      -C*A + (1-rho)*C*v-rho*v^2/2 + a*v + a^2/(2*rho) := by
    have heq : (-C*A + (1-rho)*C*v-rho*v^2/2 + a*v + a^2/(2*rho)) -
        (-C*A + (1-rho)*C*e-rho*e^2/2 + a*e) =
        rho/2*(e-v-a/rho)^2 + (e-v)*(rho*v-(1-rho)*C) := by
      field_simp <;> ring
    have hh := add_nonneg (mul_nonneg (by positivity : (0 : ℝ) ≤ rho/2)
      (sq_nonneg (e-v-a/rho))) hproj
    rw [← heq] at hh
    linarith only [hh]
  dsimp only [FrontierMain]
  change C*e-C*A-P-U ≤ -C*A+(1-rho)*C*v-rho*v^2/2 + a*v + a^2/(2*rho)+err
  linarith only [hP, hU, hq]

theorem actual_resource_frontier_bound {rho : ℝ} {C A M e : ℕ}
    (hrho : 0 < rho) (hAe : A ≤ e) (heM : e ≤ M)
    (hF : rho * C - 17 / 200 ≤ TotientRows208.TotientMass C)
    (hU : rho * (e : ℝ)^2 / 2 - (61 / 200) * e ≤ TotientTriangle e) :
    (ResourceCount C A M e : ℝ) ≤
      (coprimeRectangle C M).card + (TotientTriangle M : ℝ) +
      FrontierMain rho C A + (39 / 100 : ℝ) * max (A : ℝ) ((1 / rho - 1) * C) +
      (39 / 100 : ℝ)^2 / (2 * rho) + (C : ℝ) / 2 * Real.log C := by
  have hP := TotientRows208.rectangle_local_lower (e := e) hF
  have hP' : rho * C * e - ((39 / 100 : ℝ) - 61 / 200) * e -
      (C : ℝ) / 2 * Real.log C ≤ (coprimeRectangle C e).card := by
    norm_num at hP ⊢
    exact hP
  have hf := frontier_complete_square (A := (A : ℝ)) hrho (by norm_num : (0 : ℝ) ≤ 39 / 100)
    (by exact_mod_cast hAe) hP' hU
  rw [resource_frontier_identity hAe heM]
  linarith only [hf]

theorem frontier_main_deficit {rho C A : ℝ} (hrho : 200 / 329 ≤ rho)
    (hrho1 : rho ≤ 1) (hC : 0 ≤ C) (hA : 0 ≤ A) :
    FrontierMain rho C A - C^2 / 2 ≤ -(23359 / 80000 : ℝ) * (C + A)^2 := by
  have hrho0 : 0 < rho := by linarith only [hrho]
  let alpha : ℝ := 129 / 200
  let v := max A ((1 / rho - 1) * C)
  have hCAsq : 0 ≤ C * A := mul_nonneg hC hA
  have hC2 : 0 ≤ C^2 := sq_nonneg C
  have hA2 : 0 ≤ A^2 := sq_nonneg A
  have hratio : (1 / rho - 1) ≤ alpha := by
    apply (sub_le_iff_le_add).mpr
    apply (div_le_iff₀ hrho0).mpr
    dsimp only [alpha]
    nlinarith only [hrho]
  by_cases hAv : A ≤ (1 / rho - 1) * C
  · have hvEq : v = (1 / rho - 1) * C := max_eq_right hAv
    have hcenter : rho * v = (1-rho)*C := by rw [hvEq]; field_simp <;> ring
    have hv0 : 0 ≤ v := hA.trans (le_max_left _ _)
    have hvhi : v ≤ alpha * C := by rw [hvEq]; exact mul_le_mul_of_nonneg_right hratio hC
    have hAhi : A ≤ alpha * C := (le_max_left _ _).trans hvhi
    have hv2 : v^2 ≤ alpha^2 * C^2 := by nlinarith only [hv0, hvhi, sq_nonneg (v-alpha*C)]
    have hrhov : rho * v^2 ≤ v^2 := mul_le_of_le_one_left (sq_nonneg v) hrho1
    have hacross := mul_le_mul_of_nonneg_right hAhi hA
    have hmain : FrontierMain rho C A = -C*A + rho*v^2/2 := by
      dsimp only [FrontierMain]
      change -C*A+(1-rho)*C*v-rho*v^2/2 = _
      nlinarith only [congrArg (fun x : ℝ => x*v) hcenter]
    rw [hmain]
    dsimp only [alpha] at hv2 hacross
    nlinarith only [hv2, hrhov, hacross, hCAsq]
  · have hvEq : v = A := max_eq_left (le_of_not_ge hAv)
    have hmain : FrontierMain rho C A = -rho*C*A-rho*A^2/2 := by
      dsimp only [FrontierMain]
      change -C*A+(1-rho)*C*v-rho*v^2/2 = _
      rw [hvEq]
      ring
    have hCA := mul_le_mul_of_nonneg_right hrho hCAsq
    have hAA := mul_le_mul_of_nonneg_right hrho hA2
    rw [hmain]
    nlinarith only [hCA, hAA, hC2, hCAsq, hA2]

#print axioms actual_triangle_totient
#print axioms resource_frontier_identity
#print axioms frontier_complete_square
#print axioms actual_resource_frontier_bound
#print axioms frontier_main_deficit
end
end JSP233.LocalizedMiddle208
