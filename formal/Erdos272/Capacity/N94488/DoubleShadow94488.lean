module

public import Erdos272.Counting.N94488.UnitFrame94488
public import Erdos272.Capacity.N94488.ShadowOverlap94488
public import Erdos272.Capacity.N94488.ShadowScalars94488
public import Erdos272.Counting.N94488.APTailThree94488

@[expose] public section

namespace JSP233.DoubleShadow94488
open StarCompletion APGeometry HarmonicAbel29 UnitCount218 IntrinsicTriples208
open APShadowCapacity16858 IntervalFamilyEndpoints16858 StepTwoGeometry94488
open scoped Classical BigOperators
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2000000

theorem shadow_union (U V : Finset (Finset ℤ)) :
    APShadow (U ∪ V) = APShadow U ∪ APShadow V := by
  ext Q
  simp only [APShadow, Finset.mem_biUnion, Finset.mem_union]
  aesop

theorem actual_joint {N : ℕ} {F : Finset (Finset ℤ)} {g : ℝ}
    (hN : 2 ≤ N) (hg : 0 < g) (hcap : 4*g*((N-1 : ℕ) : ℝ) ≤ 1)
    (hF : Legal (Ground N) F) :
    ((F.filter IsAP).card : ℝ)+6*g*(∑ S ∈ F, ((Pool S).card : ℝ)) ≤
      (129/800 : ℝ)*(N : ℝ)^2+(N : ℝ)*Harmonic N+
        (7*g/8)*((N-1 : ℕ) : ℝ)^3+73/(24000*g^2) := by
  obtain ⟨c, A, B, hsum, henv, hD, hcount, hshadow⟩ := UnitFrame94488.actual_unit_frame hF
  let D := Pairs c A B (UnitAP F)
  let K : ℝ := D.card
  let w : ℝ := (A : ℝ)+B
  let p : ℝ := (A : ℝ)*B
  let n : ℝ := (N-1 : ℕ)
  let s₁ : ℝ := (APShadow (UnitAP F)).card
  let s₂ : ℝ := (APShadow (StepTwo F)).card
  let H : ℝ := 1/(6*g)
  change 4*g*n ≤ 1 at hcap
  change ((UnitAP F).card : ℝ) ≤ w+K at hcount
  have hH : 0 < H := by dsimp only [H]; positivity
  have hgH : 6*g*H = 1 := by dsimp only [H]; field_simp [hg.ne']
  have hw : 0 ≤ w := by dsimp only [w]; positivity
  have hwn : w ≤ n := by
    dsimp only [w, n]
    exact_mod_cast hsum
  have hn : 0 ≤ n := Nat.cast_nonneg _
  have hnH : n ≤ 3*H/2 := by
    apply (mul_le_mul_iff_right₀ hg).mp
    nlinarith only [hcap, hgH]
  have hKp : K ≤ p := by
    have hc := Finset.card_le_card hD
    simp only [Finset.product_eq_sprod, Finset.card_product, Finset.card_range] at hc
    change D.card ≤ A*B at hc
    dsimp only [K, p]
    exact_mod_cast hc
  have hpw : p ≤ w^2/4 := by
    have hh := sq_nonneg ((A : ℝ)-B)
    dsimp only [p, w]
    nlinarith only [hh]
  have hmoment : ∀ x : ℝ, 0 ≤ x → w^3-6*(p-K)*(w-x)-x^3 ≤ 6*s₁+w := by
    intro x hx
    have hh := UnitFrame94488.frame_moment hD hx hshadow
    dsimp only [w, p, K, D, s₁]
    linarith only [hh]
  have hu := ShadowScalars94488.unit_scalar hH hg hgH hw (hwn.trans hnH) hKp hpw hmoment
  obtain ⟨w₂, y, hw₂, hw₂n, hy, hyw₂, htwo, hshadow₂⟩ := actual_geometry hF
  change 2*w₂ ≤ n at hw₂n
  change 8*y^3 ≤ 6*s₂+w₂ at hshadow₂
  have hyn : 4*y ≤ n := by linarith only [hyw₂, hw₂n]
  have ht := ShadowScalars94488.step_two_scalar hn hy hyn hg.le hcap
  have hshadow₂g := mul_le_mul_of_nonneg_left hshadow₂ hg.le
  have hoverlap := ShadowOverlap94488.shadow_overlap hF henv
  change 6*((APShadow (UnitAP F) ∩ APShadow (StepTwo F)).card : ℝ) ≤ w^3/8 at hoverlap
  let U := UnitAP F ∪ StepTwo F
  have hsub : U ⊆ F := Finset.union_subset (Finset.filter_subset _ _) (Finset.filter_subset _ _)
  have hAP : ∀ S ∈ U, IsAP S := by
    intro S hS
    rcases Finset.mem_union.mp hS with hS | hS <;>
      exact (Finset.mem_filter.mp hS).2.1
  have hcapacity := actual_AP_family_capacity hF hsub hAP
  rw [ground_card] at hcapacity
  have hcR : (∑ S ∈ F, ((Pool S).card : ℝ))+(APShadow U).card ≤ (N.choose 3 : ℝ) := by
    exact_mod_cast hcapacity
  have hchoose := APResidual208.cast_choose_three N
  have hncast : n = (N : ℝ)-1 := by
    dsimp only [n]
    rw [Nat.cast_sub (by omega : 1 ≤ N), Nat.cast_one]
  have hsplit : ((APShadow U).card : ℝ)+
      (APShadow (UnitAP F) ∩ APShadow (StepTwo F)).card = s₁+s₂ := by
    have hh := Finset.card_union_add_card_inter (APShadow (UnitAP F)) (APShadow (StepTwo F))
    rw [← shadow_union] at hh
    dsimp only [s₁, s₂]
    exact_mod_cast hh
  have hpool : 6*(∑ S ∈ F, ((Pool S).card : ℝ))+6*s₁+6*s₂-w^3/8 ≤ n^3-n := by
    rw [hncast]
    nlinarith only [hcR, hchoose, hsplit, hoverlap]
  have hpoolg := mul_le_mul_of_nonneg_left hpool hg.le
  have hAPcount := APTailThree94488.actual_AP_count hN hF
  have hAPloose : ((F.filter IsAP).card : ℝ) ≤
      K+y^2+(79/800 : ℝ)*(N : ℝ)^2+(N : ℝ)*Harmonic N-1/2 := by
    nlinarith only [hAPcount, hcount, htwo, hwn, hw₂n, hncast]
  have hwidthg : g*(w+w₂) ≤ 3*g*n/2 := by
    have hh := mul_le_mul_of_nonneg_left hwn hg.le
    have hh₂ := mul_le_mul_of_nonneg_left hw₂n hg.le
    linarith only [hh, hh₂]
  have hfee : (219/2000 : ℝ)*H^2 = 73/(24000*g^2) := by
    dsimp only [H]
    field_simp [hg.ne']
    <;> ring
  rw [hfee] at hu
  change ((F.filter IsAP).card : ℝ)+6*g*(∑ S ∈ F, ((Pool S).card : ℝ)) ≤
    (129/800 : ℝ)*(N : ℝ)^2+(N : ℝ)*Harmonic N+(7*g/8)*n^3+73/(24000*g^2)
  rw [hncast] at ht hpoolg hwidthg hcap ⊢
  nlinarith only [hu, ht, hshadow₂g, hpoolg, hAPloose, hwidthg, hcap,
    Nat.cast_nonneg (α := ℝ) N]

#print axioms shadow_union
#print axioms actual_joint
end
end JSP233.DoubleShadow94488
