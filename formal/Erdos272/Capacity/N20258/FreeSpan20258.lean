module

public import Erdos272.Counting.N88404.APClassFrame88404

@[expose] public section
namespace JSP233.FreeSpan20258
open StarCompletion APClasses88404 APClassFrame88404 APShadowCapacity16858
open IntervalFamilyEndpoints16858 IntervalShadowFrame291012 UnitShadowGrid218 AffineLine30
open scoped Classical BigOperators
noncomputable section
set_option autoImplicit false

/-- Eliminate the two actual arms together. The first moments control the
mixed endpoints, while the pure triples pay a cubic in the combined span. -/
private theorem scalar {A B K X Y C S a : ℝ}
    (a0 : 0 < a) (a1 : a ≤ 1) (hA : 0 ≤ A) (hB : 0 ≤ B) (hK : 0 ≤ K)
    (hX : 0 ≤ X) (hY : 0 ≤ Y) (hS : 0 ≤ S)
    (hx : K^2 ≤ B*X) (hy : K^2 ≤ A*Y)
    (count : C ≤ A+B+K) (shadow : A^3+B^3-A-B+3*(X+Y) ≤ 6*S) :
    C-a*S ≤ 1/(12*a^2)+1/a+5 := by
  let s := A+B
  let u := 1+a/6
  have hs : 0 ≤ s := add_nonneg hA hB
  by_cases pos : 0 < s
  · have moment : 4*K^2 ≤ s*(X+Y) := by
      apply (mul_le_mul_iff_right₀ pos).mp
      dsimp only [s]
      nlinarith only [mul_le_mul_of_nonneg_left hx hA,mul_le_mul_of_nonneg_left hy hB,
        mul_nonneg (sq_nonneg (A-B)) (add_nonneg hX hY)]
    have mixed : K ≤ a*(X+Y)/2+s/(8*a) := by
      apply (mul_le_mul_iff_right₀ (show 0 < 8*a by positivity)).mp
      rw [mul_add,mul_div_cancel₀ s (show 8*a ≠ 0 by positivity)]
      apply (mul_le_mul_iff_right₀ pos).mp
      nlinarith only [mul_le_mul_of_nonneg_left moment (sq_nonneg (2*a)),sq_nonneg (s-4*a*K)]
    have pure : s^3 ≤ 4*(A^3+B^3) := by
      dsimp only [s]
      nlinarith only [mul_nonneg (sq_nonneg (A-B)) (add_nonneg hA hB)]
    have cubic : C-a*S ≤ u*s+s/(8*a)-a*s^3/24 := by
      dsimp only [u,s] at *
      nlinarith only [count,mixed,mul_le_mul_of_nonneg_left shadow a0.le,
        mul_le_mul_of_nonneg_left pure a0.le]
    have identity : s/(8*a)-a*s^3/24 =
        1/(12*a^2)-(s-1/a)^2*(a*s+2)/24 := by field_simp; ring
    have loss := mul_nonneg (sq_nonneg (s-1/a)) (mul_nonneg a0.le hs)
    have gain := sq_nonneg (s-1/a-6*u)
    have const : u*(1/a)=1/a+1/6 := by dsimp only [u]; field_simp
    have umax : u^2 ≤ (7/6 : ℝ)^2 :=
      pow_le_pow_left₀ (by dsimp only [u]; positivity) (by dsimp only [u]; linarith only [a1]) 2
    nlinarith only [cubic,identity,loss,gain,const,umax]
  · have zero : A=0 ∧ B=0 := by dsimp only [s] at pos; constructor <;> linarith
    rw [zero.2,zero_mul] at hx
    have zK : K=0 := by nlinarith only [hx,hK]
    rw [zero.1,zero.2,zK] at count
    have rhs : (0 : ℝ) ≤ 1/(12*a^2)+1/a+5 := by positivity
    linarith only [count,mul_nonneg a0.le hS,rhs]

/-- Apply the price to a rooted family of intervals of any span. This
also permits the virtual intervals contained in an already covered interval. -/
theorem intervals {N : ℕ} {c : ℤ} {U : Finset (Finset ℤ)} {a : ℝ}
    (a0 : 0 < a) (a1 : a ≤ 1)
    (hc : c ∈ Ground N) (ground : ∀ S ∈ U, S ⊆ Ground N)
    (root : ∀ S ∈ U, c ∈ S) (interval : ∀ S ∈ U, ∃ l r : ℤ, S=Finset.Icc l r)
    (two : ∀ S ∈ U, 2 ≤ S.card) :
    (U.card : ℝ)-a*((APShadow U).card : ℝ) ≤ 1/(12*a^2)+1/a+5 := by
  obtain ⟨A,B,_,grid,count,shadow⟩ := actual_frame hc ground root interval two
  let D := Pairs c A B U
  let X := ∑ p ∈ D, (2*(p.1 : ℝ)+1)
  let Y := ∑ p ∈ D, (2*(p.2 : ℝ)+1)
  have totals : X+Y=2*(∑ p ∈ D, ((p.1 : ℝ)+p.2+1)) := by
    dsimp only [X,Y]
    rw [←Finset.sum_add_distrib,Finset.mul_sum]
    exact Finset.sum_congr rfl (fun p _ => by ring)
  apply scalar (X := X) (Y := Y) a0 a1 (Nat.cast_nonneg A) (Nat.cast_nonneg B) (Nat.cast_nonneg D.card)
    (by dsimp only [X]; positivity) (by dsimp only [Y]; positivity) (Nat.cast_nonneg _)
    (rectangle_x_moment grid) (rectangle_y_moment grid) count
  rw [totals]
  dsimp only [D] at *
  linarith only [shadow]

theorem actual_step {N d : ℕ} {F : Finset (Finset ℤ)} {a : ℝ}
    (hN : 1 ≤ N) (hd : 0 < d) (legal : Legal (Ground N) F) (a0 : 0 < a) (a1 : a ≤ 1) :
    ((StepAP F d).card : ℝ)-a*((APShadow (StepAP F d)).card : ℝ) ≤ 1/(12*a^2)+1/a+5 := by
  obtain ⟨f⟩ := frame_nonempty hN hd legal
  have bound := intervals a0 a1 f.root_ground f.ground f.common_root f.intervals f.card_two
  have pos : (0 : ℤ) < d := by exact_mod_cast hd
  have size := mapFamily_card f.offset (d : ℤ) pos f.family
  have triples := AffineShadow94488.map_shadow_card f.offset (d : ℤ) pos f.family
  rw [f.mapped] at size triples
  simpa only [size,triples] using bound

#print axioms intervals
#print axioms actual_step
end
end JSP233.FreeSpan20258
