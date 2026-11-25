module

public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Ring

@[expose] public section
namespace JSP233.IntervalGapBounds20258
set_option autoImplicit false

/-- Four times the unrounded bound. Dividing by four after maximization
gives the exact maximum of the integer bounds. -/
def score (s m L i : ℤ) : ℤ := (s+2-i)^2-4*max 0 (L+1-i*m)

private theorem convex {x y z : ℤ} (c p k : ℤ) (xy : x ≤ y) (yz : y ≤ z) :
    (c-y)^2+p*y+k ≤ max ((c-x)^2+p*x+k) ((c-z)^2+p*z+k) := by
  by_cases slope : x+y-2*c+p ≤ 0
  · apply le_trans _ (le_max_left _ _)
    nlinarith only [mul_nonpos_of_nonneg_of_nonpos (sub_nonneg.mpr xy) slope]
  · apply le_trans _ (le_max_right _ _)
    have pos : 0 ≤ y+z-2*c+p := by omega
    nlinarith only [mul_nonneg (sub_nonneg.mpr yz) pos]

/-- The length before the change of slope may be clipped to the entire grid. -/
theorem corners {s m L i j : ℤ} (hm : 0 ≤ m) (one : 1 ≤ i) (fits : i ≤ s)
    (jone : 1 ≤ j) (js : j ≤ s) (before : j*m ≤ L) (after : j = s ∨ L < (j+1)*m) :
    score s m L i ≤ max (score s m L 1) (max (score s m L j) (score s m L (min s (j+1)))) := by
  have quadratic (t : ℤ) (ht : t ≤ j) :
      score s m L t = (s+2-t)^2+(4*m)*t-4*(L+1) := by
    have le := (mul_le_mul_of_nonneg_right ht hm).trans before
    unfold score
    rw [max_eq_right (by omega)]
    ring
  by_cases early : i ≤ j
  · have bound := convex (s+2) (4*m) (-(4*(L+1))) one early
    simp only [←sub_eq_add_neg] at bound
    rw [quadratic i early,quadratic 1 jone,quadratic j le_rfl]
    exact bound.trans (max_le_max le_rfl (le_max_left _ _))
  · have next : j+1 ≤ s := by omega
    have paid : L < (j+1)*m := after.resolve_left (by omega)
    have covered : L < i*m := paid.trans_le (mul_le_mul_of_nonneg_right (by omega) hm)
    apply le_trans _ ((le_max_right _ _).trans (le_max_right _ _))
    unfold score
    rw [min_eq_right next,max_eq_left (by omega : L+1-i*m ≤ 0),
      max_eq_left (by omega : L+1-(j+1)*m ≤ 0)]
    have prod := mul_nonneg (show 0 ≤ i-(j+1) by omega)
      (show 0 ≤ (s+2-i)+(s+2-(j+1)) by omega)
    nlinarith only [prod]

/-- Convert the physical rectangular count to its one-dimensional score. -/
theorem rectangle {s m L D g C i u v : ℤ} (pos : 0 < D)
    (right : 0 ≤ u) (left : 0 ≤ v) (size : i+u+v ≤ s)
    (many : L*D < g) (rect : C ≤ (u+1)*(v+1))
    (joint : g+C*D ≤ (i*m+(u+1)*(v+1))*D) :
    4*C ≤ score s m L i := by
  have strict : (L+C)*D < (i*m+(u+1)*(v+1))*D := by
    rw [add_mul]
    linarith only [many,joint]
  have pay := (mul_lt_mul_iff_left₀ pos).mp strict
  have prod := mul_nonneg (show 0 ≤ s-i-u-v by omega)
    (show 0 ≤ (s+2-i)+(u+v+2) by omega)
  have area : 4*((u+1)*(v+1)) ≤ (s+2-i)^2 := by
    nlinarith only [prod,sq_nonneg (u-v)]
  unfold score
  rcases le_total (L+1-i*m) 0 with paid | needed
  · rw [max_eq_left paid]
    linarith only [rect,area]
  · rw [max_eq_right needed]
    omega

def limit (s m L : ℕ) : ℤ :=
  let j : ℤ := (min s (L/m) : ℕ)
  max 0 (max (score s m L 1) (max (score s m L j) (score s m L (min (s : ℤ) (j+1)))))

theorem limit_nonneg (s m L : ℕ) : 0 ≤ limit s m L := le_max_left _ _

theorem score_le_limit {s m L i : ℕ} (hm : 0 < m) (level : m ≤ L)
    (one : 1 ≤ i) (fits : i ≤ s) : score s m L i ≤ limit s m L := by
  let j := min s (L/m)
  have jone : 1 ≤ j := le_min (one.trans fits)
    ((Nat.le_div_iff_mul_le hm).mpr (by simpa using level))
  have js : j ≤ s := min_le_left _ _
  have before : j*m ≤ L :=
    (Nat.mul_le_mul_right m (min_le_right s (L/m))).trans (Nat.div_mul_le_self _ _)
  have after : (j : ℤ) = s ∨ (L : ℤ) < ((j : ℤ)+1)*m := by
    by_cases h : s ≤ L/m
    · exact Or.inl (by change ((min s (L/m) : ℕ) : ℤ) = s; rw [min_eq_left h])
    · right
      have bound : L < (j+1)*m := by
        dsimp [j]
        rw [min_eq_right (by omega),Nat.mul_comm]
        exact Nat.lt_mul_div_succ L hm
      exact_mod_cast bound
  exact (corners (Int.natCast_nonneg m) (by exact_mod_cast one) (by exact_mod_cast fits)
    (by exact_mod_cast jone : (1 : ℤ) ≤ j) (by exact_mod_cast js) (by exact_mod_cast before) after).trans
    (le_max_right _ _)

#print axioms corners
#print axioms rectangle
end JSP233.IntervalGapBounds20258
