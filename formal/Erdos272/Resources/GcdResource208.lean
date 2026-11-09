module

public import Erdos272.Resources.ResourceSymmetry56
public import Erdos272.Foundation.ProofTactics
public import Mathlib.Data.Real.Basic
public import Mathlib.Algebra.BigOperators.Ring.Finset
public import Mathlib.Order.Interval.Finset.Nat

@[expose] public section

/-! Exact gcd decomposition of the actual finite coprime resource pools. -/
namespace JSP233.GcdResource208
open CoprimeDensity52 MiddleJoint51 ResourceSymmetry56
open scoped Classical BigOperators
noncomputable section
set_option maxHeartbeats 0

def RectangleCodes (X Y N : ℕ) : Finset (Σ _ : ℕ, ℕ × ℕ) :=
  (Finset.Icc 1 N).sigma fun d => coprimeRectangle (X / d) (Y / d)

theorem primitive_rectangle_sum {X Y N : ℕ} (hXN : X ≤ N) :
    (∑ d ∈ Finset.Icc 1 N, (coprimeRectangle (X / d) (Y / d)).card) = X * Y := by
  let f : (Σ _ : ℕ, ℕ × ℕ) → ℕ × ℕ := fun u => (u.1 * u.2.1, u.1 * u.2.2)
  have hc : (RectangleCodes X Y N).card = ((Finset.Icc 1 X).product (Finset.Icc 1 Y)).card := by
    apply Finset.card_bij (fun u _ => f u)
    · intro u hu
      obtain ⟨hd, hp⟩ := Finset.mem_sigma.mp hu
      obtain ⟨hdpos, hdN⟩ := Finset.mem_Icc.mp hd
      obtain ⟨hi, hiX, hj, hjY, hcop⟩ := mem_rectangle.mp hp
      have hiMul := (Nat.le_div_iff_mul_le hdpos).mp hiX
      have hjMul := (Nat.le_div_iff_mul_le hdpos).mp hjY
      exact Finset.mem_product.mpr ⟨Finset.mem_Icc.mpr ⟨Nat.mul_pos hdpos hi,
        by dsimp only [f]; nlinarith only [hiMul]⟩,
        Finset.mem_Icc.mpr ⟨Nat.mul_pos hdpos hj,
          by dsimp only [f]; nlinarith only [hjMul]⟩⟩
    · intro u hu v hv heq
      obtain ⟨hud, hup⟩ := Finset.mem_sigma.mp hu
      obtain ⟨hvd, hvp⟩ := Finset.mem_sigma.mp hv
      have hdpos := (Finset.mem_Icc.mp hud).1
      have hucop := (mem_rectangle.mp hup).2.2.2.2
      have hvcop := (mem_rectangle.mp hvp).2.2.2.2
      have hgu : (f u).1.gcd (f u).2 = u.1 := by
        dsimp only [f]
        rw [Nat.gcd_mul_left, hucop.gcd_eq_one, Nat.mul_one]
      have hgv : (f v).1.gcd (f v).2 = v.1 := by
        dsimp only [f]
        rw [Nat.gcd_mul_left, hvcop.gcd_eq_one, Nat.mul_one]
      have hdEq : u.1 = v.1 := hgu.symm.trans ((congrArg (fun p : ℕ × ℕ => p.1.gcd p.2) heq).trans hgv)
      have hiEq := congrArg Prod.fst heq
      have hjEq := congrArg Prod.snd heq
      dsimp only [f] at hiEq hjEq
      rw [← hdEq] at hiEq hjEq
      exact Sigma.ext hdEq (heq_of_eq (Prod.ext
        (Nat.eq_of_mul_eq_mul_left hdpos hiEq) (Nat.eq_of_mul_eq_mul_left hdpos hjEq)))
    · intro p hp
      obtain ⟨hx, hy⟩ := Finset.mem_product.mp hp
      obtain ⟨hxpos, hxX⟩ := Finset.mem_Icc.mp hx
      obtain ⟨hypos, hyY⟩ := Finset.mem_Icc.mp hy
      let g := p.1.gcd p.2
      have hg : 0 < g := Nat.gcd_pos_of_pos_left p.2 hxpos
      have hgx : g ∣ p.1 := Nat.gcd_dvd_left p.1 p.2
      have hgy : g ∣ p.2 := Nat.gcd_dvd_right p.1 p.2
      have hgN : g ≤ N := (Nat.gcd_le_left p.2 hxpos).trans (hxX.trans hXN)
      refine ⟨⟨g, p.1 / g, p.2 / g⟩, Finset.mem_sigma.mpr
        ⟨Finset.mem_Icc.mpr ⟨hg, hgN⟩, mem_rectangle.mpr ?_⟩, ?_⟩
      · exact ⟨Nat.div_pos (Nat.le_of_dvd hxpos hgx) hg, Nat.div_le_div_right hxX,
          Nat.div_pos (Nat.le_of_dvd hypos hgy) hg, Nat.div_le_div_right hyY,
          Nat.coprime_div_gcd_div_gcd hg⟩
      · exact Prod.ext (Nat.mul_div_cancel' hgx) (Nat.mul_div_cancel' hgy)
  simpa only [RectangleCodes, Finset.card_sigma, Finset.product_eq_sprod,
    Finset.card_product, Nat.card_Icc, Nat.add_sub_cancel] using hc

theorem primitive_triangle_sum (M : ℕ) :
    2 * (∑ d ∈ Finset.Icc 1 M, (UpperTriangle 0 (M / d)).card) + M = M^2 := by
  have hrow : ∀ d ∈ Finset.Icc 1 M,
      2 * (UpperTriangle 0 (M / d)).card + 1 =
        (coprimeRectangle (M / d) (M / d)).card := by
    intro d hd
    obtain ⟨hdpos, hdM⟩ := Finset.mem_Icc.mp hd
    have hpos : 0 < M / d := Nat.div_pos hdM hdpos
    simpa only [if_pos hpos] using actual_square_symmetry (M / d)
  have hs := Finset.sum_congr rfl hrow
  rw [Finset.sum_add_distrib, ← Finset.mul_sum, Finset.sum_const] at hs
  simp only [Nat.card_Icc, Nat.add_sub_cancel, smul_eq_mul, mul_one] at hs
  rw [primitive_rectangle_sum (Y := M) (N := M) le_rfl] at hs
  nlinarith only [hs]

theorem primitive_triangle_sum_to {M N : ℕ} (hMN : M ≤ N) :
    2 * (∑ d ∈ Finset.Icc 1 N, (UpperTriangle 0 (M / d)).card) + M = M^2 := by
  have hsub : Finset.Icc 1 M ⊆ Finset.Icc 1 N := by
    intro d hd
    obtain ⟨hd1, hdM⟩ := Finset.mem_Icc.mp hd
    exact Finset.mem_Icc.mpr ⟨hd1, hdM.trans hMN⟩
  have heq : (∑ d ∈ Finset.Icc 1 N, (UpperTriangle 0 (M / d)).card) =
      ∑ d ∈ Finset.Icc 1 M, (UpperTriangle 0 (M / d)).card := by
    symm
    apply Finset.sum_subset hsub
    intro d hdN hdM
    have hMd : M < d := by
      have hd1 := (Finset.mem_Icc.mp hdN).1
      simp only [Finset.mem_Icc, not_and_or, not_le] at hdM
      omega
    simp [Nat.div_eq_of_lt hMd, UpperTriangle, CoprimeBox]
  rw [heq]
  exact primitive_triangle_sum M

theorem physical_base_identity {c R N : ℕ} (hcR : c ≤ R) (hRN : R ≤ N) :
    ((∑ d ∈ Finset.Icc 1 N,
      ((coprimeRectangle (c / d) ((R - c) / d)).card +
        (UpperTriangle 0 ((R - c) / d)).card) : ℕ) : ℝ) =
      (R : ℝ)^2 / 2 - (c : ℝ)^2 / 2 - ((R : ℝ) - c) / 2 := by
  have hr := primitive_rectangle_sum (Y := R - c) (hcR.trans hRN)
  have ht := primitive_triangle_sum_to ((Nat.sub_le R c).trans hRN)
  have hrR : ((∑ d ∈ Finset.Icc 1 N,
      (coprimeRectangle (c / d) ((R - c) / d)).card : ℕ) : ℝ) =
      (c : ℝ) * ((R : ℝ) - c) := by exact_mod_cast hr
  have htR : 2 * ((∑ d ∈ Finset.Icc 1 N,
      (UpperTriangle 0 ((R - c) / d)).card : ℕ) : ℝ) + ((R : ℝ) - c) =
      ((R : ℝ) - c)^2 := by exact_mod_cast ht
  rw [Finset.sum_add_distrib, Nat.cast_add]
  linarith only [hrR, htR]

#print axioms primitive_rectangle_sum
#print axioms primitive_triangle_sum
#print axioms physical_base_identity
end
end JSP233.GcdResource208
