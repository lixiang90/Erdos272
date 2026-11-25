module

public import Erdos272.Capacity.N20258.ResidueCapacity20258
public import Erdos272.Capacity.N20258.FreeSpan20258
public import Erdos272.Counting.N20258.MatchedTails20258
public import Erdos272.Arithmetic.N291012.ShadowResponse291012

@[expose] public section
namespace JSP233.ResidueJoint20258
open StarCompletion APGeometry APShadowCapacity16858 IntrinsicTriples208
open APClasses88404 APClassFrame88404 ResidueCapacity20258 ProgressionPartition20258
open scoped BigOperators Classical
noncomputable section
set_option autoImplicit false

private theorem coefficient_range (ps : List ℕ) (k : ℕ)
    (h : (ps.map CubicSieve20258.density).sum < 1) :
    1-(ps.map CubicSieve20258.density).sum ≤ CubicSieve20258.coefficient ps k ∧
      CubicSieve20258.coefficient ps k ≤ 1 := by
  induction ps generalizing k with
  | nil => simp [CubicSieve20258.coefficient]
  | cons p ps ih =>
    have hp : 0 ≤ CubicSieve20258.density p := by unfold CubicSieve20258.density; positivity
    simp only [List.map_cons, List.sum_cons] at h ⊢
    have hs : (ps.map CubicSieve20258.density).sum < 1 := by linarith only [hp,h]
    cases k with
    | zero =>
      have hn : 0 ≤ (ps.map CubicSieve20258.density).sum := by
        apply List.sum_nonneg
        intro a ha
        obtain ⟨j,_,rfl⟩ := List.mem_map.mp ha
        unfold CubicSieve20258.density
        positivity
      simp only [CubicSieve20258.coefficient]
      exact ⟨by linarith only [hp,hn], le_rfl⟩
    | succ k =>
      obtain ⟨l,u⟩ := ih (k+1) hs
      obtain ⟨lk,uk⟩ := ih k hs
      have hlo := mul_nonneg hp (by linarith only [lk,hs] : 0 ≤ CubicSieve20258.coefficient ps k)
      have hhi := mul_le_mul_of_nonneg_left uk hp
      rw [CubicSieve20258.coefficient]
      constructor <;> linarith only [hlo,hhi,l,u]

theorem beta_range {d : ℕ} (hd : d ∈ steps) : 0 < beta d ∧ beta d ≤ 1 := by
  have h := (by decide +kernel : ∀ j ∈ PairError20258.steps,
    ((later j).map CubicSieve20258.density).sum < 1) d (List.mem_toFinset.mp hd)
  obtain ⟨l,u⟩ := coefficient_range (later d) 3 h
  exact ⟨by unfold beta; linarith only [l,h], u⟩

def response (N d : ℕ) (x : ℝ) : ℝ :=
  let w : ℝ := ((N-1)/d : ℕ)
  let a : ℝ := beta d
  w + a*w/(6*x) + if d = 1 then x^2/(12*a^2) else w^2/4-a*w^3/(6*x)

theorem class_response {N d : ℕ} {F : Finset (Finset ℤ)} {x : ℝ}
    (hN : 1 ≤ N) (hd : d ∈ steps) (hx : 0 < x) (hxN : (N : ℝ)-1 ≤ 2*x)
    (legal : Legal (Ground N) F) :
    ((StepAP F d).card : ℝ)-(beta d : ℝ)*((APShadow (StepAP F d)).card : ℝ)/x ≤
      response N d x := by
  obtain ⟨f⟩ := frame_nonempty hN (positive hd) legal
  obtain ⟨y,hy,hyf,hcount,hshadow⟩ := geometry f (positive hd)
  let w : ℝ := ((N-1)/d : ℕ)
  let a : ℝ := beta d
  have ha : 0 < a := by dsimp only [a]; exact_mod_cast (beta_range hd).1
  have ha1 : a ≤ 1 := by dsimp only [a]; exact_mod_cast (beta_range hd).2
  have hspan : d*(f.size-1) ≤ N-1 := by
    have hr : (d : ℝ)*((f.size-1 : ℕ) : ℝ) ≤ ((N-1 : ℕ) : ℝ) := by
      simpa only [Nat.cast_sub f.size_positive, Nat.cast_sub hN, Nat.cast_one] using f.span
    exact_mod_cast hr
  have hfloor : f.size-1 ≤ (N-1)/d := (Nat.le_div_iff_mul_le (positive hd)).mpr (by simpa [Nat.mul_comm] using hspan)
  have hw : (f.size : ℝ)-1 ≤ w := by
    have h : ((f.size-1 : ℕ) : ℝ) ≤ w := by dsimp only [w]; exact_mod_cast hfloor
    simpa only [Nat.cast_sub f.size_positive, Nat.cast_one] using h
  let g := a/(6*x)
  have hg : 0 < g := div_pos ha (by positivity)
  have hgx : g*(6*x) = a := div_mul_cancel₀ _ (by positivity)
  have mass := mul_le_mul_of_nonneg_left hshadow hg.le
  have wh := mul_le_mul_of_nonneg_left hw hg.le
  have price : a*((APShadow (StepAP F d)).card : ℝ)/x =
      6*g*((APShadow (StepAP F d)).card : ℝ) := by unfold g; field_simp
  have lin : a*w/(6*x)=g*w := by unfold g; ring
  rw [price]
  change _ ≤ w+a*w/(6*x)+_
  rw [lin]
  by_cases unit : d=1
  · rw [ite_eq_left unit]
    have max := ShadowResponse291012.cubic_max hy hg
    have eqn : 1/(432*g^2)=x^2/(12*a^2) := by unfold g; field_simp; ring
    rw [eqn] at max
    linarith only [hcount,hw,wh,mass,max]
  · rw [ite_eq_right unit]
    have dd : 2 ≤ d := by have := positive hd; omega
    have wd : w*(d : ℝ) ≤ (N : ℝ)-1 := by
      have hn := Nat.div_mul_le_self (N-1) d
      have hc : w*(d : ℝ) ≤ ((N-1 : ℕ) : ℝ) := by dsimp only [w]; exact_mod_cast hn
      simpa only [Nat.cast_sub hN, Nat.cast_one] using hc
    have wpos : 0 ≤ w := Nat.cast_nonneg _
    have w2 := mul_le_mul_of_nonneg_left (show (2 : ℝ) ≤ d by exact_mod_cast dd) wpos
    have aw := mul_le_mul_of_nonneg_right ha1 wpos
    have lim : 12*g*(w/2) ≤ 1 := by
      apply (mul_le_mul_iff_left₀ hx).mp
      nlinarith only [hgx,wd,w2,aw,hxN]
    have max := SieveScalars88404.endpoint_cubic hg.le hy (by linarith only [hyf,hw] : y ≤ w/2) lim
    have eqn : (w/2)^2-8*g*(w/2)^3 = w^2/4-a*w^3/(6*x) := by unfold g; ring
    rw [eqn] at max
    linarith only [hcount,hw,wh,mass,max]

theorem steps_in_ground {N : ℕ} (hN : 62 ≤ N) : steps ⊆ Finset.Icc 1 (N-1) := by
  intro d hd
  have h := (by decide +kernel : ∀ j ∈ PairError20258.steps, j ≤ 61) d (List.mem_toFinset.mp hd)
  exact Finset.mem_Icc.mpr ⟨positive hd, by omega⟩

/-- The selected progression classes and the intrinsic pools use the same
triple capacity. The unselected classes can be estimated separately. -/
theorem priced_classes {N : ℕ} {F : Finset (Finset ℤ)} {x : ℝ}
    (hN : 1 ≤ N) (hx : 0 < x) (hxN : (N : ℝ)-1 ≤ 2*x) (legal : Legal (Ground N) F)
    : (∑ d ∈ steps, ((StepAP F d).card : ℝ))+(∑ S ∈ F, ((Pool S).card : ℝ))/x ≤
      (∑ d ∈ steps, response N d x)+
      ((N.choose 3 : ℝ)+(99*((N : ℝ)-1)^2+210*((N : ℝ)-1)+120)/1000)/x := by
  have sum := Finset.sum_le_sum fun d hd => class_response hN hd hx hxN legal
  rw [Finset.sum_sub_distrib, ←Finset.sum_div] at sum
  have cap := (Rat.cast_le (K := ℝ)).mpr (ResidueCapacity20258.actual_capacity hN legal)
  push_cast at cap
  have paid := div_le_div_of_nonneg_right cap hx.le
  rw [add_div] at paid
  linarith only [sum,paid]

/-- On the unit grid the actual span may be smaller than the ambient.
Take the better of the two certified responses. -/
def spanResponse (N d : ℕ) (x : ℝ) : ℝ :=
  if d=1 then
    let a : ℝ := (beta d : ℝ)/x
    min (response N d x) (1/(12*a^2)+1/a+5)
  else response N d x

theorem priced_spans {N : ℕ} {F : Finset (Finset ℤ)} {x : ℝ}
    (hN : 1 ≤ N) (hx : 1 ≤ x) (span : (N : ℝ)-1 ≤ 2*x) (legal : Legal (Ground N) F) :
    (∑ d ∈ steps, ((StepAP F d).card : ℝ))+(∑ S ∈ F, ((Pool S).card : ℝ))/x ≤
      (∑ d ∈ steps, spanResponse N d x)+
      ((N.choose 3 : ℝ)+(99*((N : ℝ)-1)^2+210*((N : ℝ)-1)+120)/1000)/x := by
  have pos : 0 < x := by linarith
  have each (d : ℕ) (hd : d ∈ steps) :
      ((StepAP F d).card : ℝ)-(beta d : ℝ)*((APShadow (StepAP F d)).card : ℝ)/x ≤ spanResponse N d x := by
    have basic := class_response hN hd pos span legal
    by_cases unit : d=1
    · rw [spanResponse,ite_eq_left unit]
      apply le_min basic
      have bp : (0 : ℝ) < (beta d : ℝ) := by exact_mod_cast (beta_range hd).1
      have bu : (beta d : ℝ) ≤ 1 := by exact_mod_cast (beta_range hd).2
      have sharp := FreeSpan20258.actual_step hN (positive hd) legal (div_pos bp pos)
        ((div_le_one pos).mpr (bu.trans hx))
      simpa only [div_mul_eq_mul_div] using sharp
    · simpa only [spanResponse,ite_eq_right unit] using basic
  have sum := Finset.sum_le_sum each
  rw [Finset.sum_sub_distrib,←Finset.sum_div] at sum
  have cap := (Rat.cast_le (K := ℝ)).mpr (ResidueCapacity20258.actual_capacity hN legal)
  push_cast at cap
  have paid := div_le_div_of_nonneg_right cap pos.le
  rw [add_div] at paid
  linarith only [sum,paid]

private theorem joint_of_partition {N k credit : ℕ} {F : Finset (Finset ℤ)} {x : ℝ}
    (hN : 1 ≤ N) (hx : 0 < x) (hxN : (N : ℝ)-1 ≤ 2*x) (legal : Legal (Ground N) F)
    (total : (F.filter IsAP).card+credit ≤ 1+(∑ d ∈ steps, (StepAP F d).card)+offTail (N-1) k steps) :
    ((F.filter IsAP).card : ℝ)+credit+(∑ S ∈ F, ((Pool S).card : ℝ))/x ≤
      1+offTail (N-1) k steps+(∑ d ∈ steps, response N d x)+
      ((N.choose 3 : ℝ)+(99*((N : ℝ)-1)^2+210*((N : ℝ)-1)+120)/1000)/x := by
  have t : ((F.filter IsAP).card : ℝ)+credit ≤
      1+(∑ d ∈ steps, ((StepAP F d).card : ℝ))+offTail (N-1) k steps := by exact_mod_cast total
  linarith only [t,priced_classes hN hx hxN legal]

/-- Joint bound for the actual progression members and the intrinsic pools. -/
theorem actual_joint {N k : ℕ} {F : Finset (Finset ℤ)} {x : ℝ}
    (hN : 62 ≤ N) (hx : 0 < x) (hxN : (N : ℝ)-1 ≤ 2*x) (legal : Legal (Ground N) F)
    (hmin : ∀ d ∈ Finset.Icc 1 (N-1) \ steps, ∀ S ∈ StepAP F d, k < S.card) :
    ((F.filter IsAP).card : ℝ)+(∑ S ∈ F, ((Pool S).card : ℝ))/x ≤
      1+offTail (N-1) k steps+(∑ d ∈ steps, response N d x)+
      ((N.choose 3 : ℝ)+(99*((N : ℝ)-1)^2+210*((N : ℝ)-1)+120)/1000)/x := by
  have small : 1 ≤ N := by omega
  have total := actual_AP_partition small legal steps (steps_in_ground hN) hmin
  simpa only [Nat.cast_zero,add_zero] using joint_of_partition (credit := 0) small hx hxN legal total

/-- Count the gaps from the matched starts and price the intrinsic triples of
the same original family in one inequality. -/
theorem actual_matched_joint {N m k K j L : ℕ} {F G : Finset (Finset ℤ)} {x : ℝ}
    (hN : 62 ≤ N) (hx : 0 < x) (hxN : (N : ℝ)-1 ≤ 2*x)
    (hm : m+1 ≤ N) (hj : 0 < j) (hk : k ≤ K) (short : 2*j ≤ k+1)
    (fits : (K-j)*m+j*j ≤ L) (paid : Finset ℕ) (paidIn : paid ⊆ Finset.Icc 1 (N-1) \ steps)
    (wide : ∀ d ∈ paid, K+2*j ≤ (N-1)/d+2)
    (legal : Legal (Ground N) F) (sub : G ⊆ PrivatePairExistence.CrookedMembers F)
    (many : L*(N-2) < G.card)
    (omits : ∀ z ∈ Ground N, ∃ Q ∈ PrivatePairExistence.CrookedMembers F, z ∉ Q ∧ Q.card ≤ m)
    (hmin : ∀ d ∈ Finset.Icc 1 (N-1) \ steps, ∀ S ∈ StepAP F d, k < S.card) :
    ((F.filter IsAP).card : ℝ)+(paid.card*((K-k)*j) : ℕ)+(∑ S ∈ F, ((Pool S).card : ℝ))/x ≤
      1+offTail (N-1) k steps+(∑ d ∈ steps, response N d x)+
      ((N.choose 3 : ℝ)+(99*((N : ℝ)-1)^2+210*((N : ℝ)-1)+120)/1000)/x := by
  exact joint_of_partition (by omega) hx hxN legal (MatchedTails20258.partition (by omega) hm hj hk short
    fits steps paid (steps_in_ground hN) paidIn wide legal sub many omits hmin)

#print axioms actual_matched_joint

#print axioms actual_joint
end
end JSP233.ResidueJoint20258
