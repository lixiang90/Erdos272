module

public import Erdos272.Capacity.N88404.SieveScalars88404
public import Mathlib.Data.Set.Finite.Basic

@[expose] public section

namespace JSP233.SieveConstants88404
open scoped Classical BigOperators
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1500000

def Selected : Finset ℕ := {2,3,5,7,11,13}
def Steps : Finset ℕ := insert 1 Selected
def Later (p : ℕ) : Finset ℕ := Selected.filter (fun q => p<q)
def Alpha (p : ℕ) : ℝ := ∏ q∈Later p, (1-1/(q : ℝ)^3)
def Error (p : ℕ) : ℝ :=
  (∏ q∈Later p, (1+1/(q : ℝ)^2))+
    (1/2 : ℝ)*(∏ q∈Later p, (1-1/(q : ℝ)^2))-3/2

theorem steps_finite : (Steps : Set ℕ).Finite := Steps.finite_toSet

theorem steps_positive {p : ℕ} (hp : p∈Steps) : 0<p := by
  simp only [Steps, Selected, Finset.mem_insert, Finset.mem_singleton] at hp
  omega

theorem steps_pairwise_coprime : (Steps : Set ℕ).Pairwise Nat.Coprime := by
  intro p hp q hq hpq
  simp only [Steps, Selected, Finset.mem_coe, Finset.mem_insert, Finset.mem_singleton] at hp hq
  rcases hp with rfl|rfl|rfl|rfl|rfl|rfl|rfl <;>
    rcases hq with rfl|rfl|rfl|rfl|rfl|rfl|rfl <;>
      first | exact False.elim (hpq rfl) | decide

theorem selected_range {p : ℕ} (hp : p∈Selected) : 2≤p ∧ p≤13 := by
  simp only [Selected, Finset.mem_insert, Finset.mem_singleton] at hp
  omega

theorem alpha_one : Alpha 1 = 32767248/39364325 := by
  norm_num [Alpha, Later, Selected, Finset.prod_filter]

theorem alpha_range {p : ℕ} (hp : p∈Steps) : 0<Alpha p ∧ Alpha p≤1 := by
  simp only [Steps, Selected, Finset.mem_insert, Finset.mem_singleton] at hp
  rcases hp with rfl|rfl|rfl|rfl|rfl|rfl|rfl <;>
    norm_num [Alpha, Later, Selected, Finset.prod_filter]

theorem alpha_cube_sum :
    (∑ p∈Selected, Alpha p/(p : ℝ)^3) = 1-Alpha 1 := by
  norm_num [Alpha, Later, Selected, Finset.prod_filter]

theorem error_values :
    Error 1=27409049/90180090 ∧ Error 2=9736777/90180090 ∧
    Error 3=399649/10020010 ∧ Error 5=35677/2004002 ∧
    Error 7=293/40898 ∧ Error 11=1/338 ∧ Error 13=0 := by
  norm_num [Error, Later, Selected, Finset.prod_filter]

theorem error_nonnegative {p : ℕ} (hp : p∈Steps) : 0≤Error p := by
  simp only [Steps, Selected, Finset.mem_insert, Finset.mem_singleton] at hp
  rcases hp with rfl|rfl|rfl|rfl|rfl|rfl|rfl <;>
    norm_num [Error, Later, Selected, Finset.prod_filter]

theorem error_sum_identity (n : ℝ) :
    (∑ p∈Steps, Error p*(n/(p : ℝ)+1)^2) =
      (606450017/1803601800 : ℝ)*n^2+(13565611/18036018 : ℝ)*n+
        (2403389/5010005 : ℝ) := by
  norm_num [Steps, Selected, Error, Later, Finset.prod_filter]
  ring

theorem error_sum_bound {n : ℝ} (hn : 1000≤n) :
    (∑ p∈Steps, Error p*(n/(p : ℝ)+1)^2) ≤ n^2/2 := by
  rw [error_sum_identity]
  exact SieveScalars88404.quadratic_error_bound hn

#print axioms steps_finite
#print axioms steps_positive
#print axioms steps_pairwise_coprime
#print axioms selected_range
#print axioms alpha_one
#print axioms alpha_range
#print axioms alpha_cube_sum
#print axioms error_values
#print axioms error_nonnegative
#print axioms error_sum_identity
#print axioms error_sum_bound
end
end JSP233.SieveConstants88404
