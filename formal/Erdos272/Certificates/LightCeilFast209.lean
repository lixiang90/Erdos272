module

public import Erdos272.Arithmetic.LightCeil209

@[expose] public section

namespace JSP233.LightCeilFast209
open ResidualCeil208
open scoped BigOperators

/-- A recursive evaluation of the same finite sum used by `LightCeil209.Upper`. -/
def sumFast (A B V E : ℕ) : ℕ → ℕ
  | 0 => 0
  | n+1 => sumFast A B V E n + LightCeil209.TermUpper V E (A+n*B)

theorem sumFast_eq (A B V E L : ℕ) :
    sumFast A B V E L =
      ∑ r ∈ Finset.range L, LightCeil209.TermUpper V E (A+r*B) := by
  induction L with
  | zero => rfl
  | succ n ih => simp only [sumFast, Finset.sum_range_succ, ih]

def upperFast (A B V E L : ℕ) : ℕ :=
  sumFast A B V E L + V*InvUpper (LightCeil209.TailDenominator A B L)

theorem upperFast_eq (A B V E L : ℕ) :
    upperFast A B V E L = LightCeil209.Upper A B V E L := by
  simp only [upperFast, LightCeil209.Upper, sumFast_eq]

def checkFast (A B V E L u : ℕ) : Bool := decide
  (0<A ∧ 0<B ∧ E<V ∧ 1≤L ∧ Grid*upperFast A B V E L≤Scale*u)

theorem checkFast_eq (A B V E L u : ℕ) :
    checkFast A B V E L u = LightCeil209.Check A B V E L u := by
  simp only [checkFast, LightCeil209.Check, upperFast_eq]

def checkAllFast (data : List (ℕ×ℕ×ℕ×ℕ×ℕ)) : Bool :=
  data.all (fun a => checkFast a.1 a.2.1 a.2.2.1 a.2.2.2.1 128 a.2.2.2.2)

theorem checkAllFast_eq (data : List (ℕ×ℕ×ℕ×ℕ×ℕ)) :
    checkAllFast data = data.all
      (fun a => LightCeil209.Check a.1 a.2.1 a.2.2.1 a.2.2.2.1 128 a.2.2.2.2) := by
  simp only [checkAllFast, checkFast_eq]

theorem checkAllFast_sound {data : List (ℕ×ℕ×ℕ×ℕ×ℕ)}
    (h : checkAllFast data = true) :
    data.all (fun a => LightCeil209.Check a.1 a.2.1 a.2.2.1 a.2.2.2.1 128 a.2.2.2.2) = true := by
  rw [← checkAllFast_eq]
  exact h

/-- Extract tuple fields while the predicate is abstract, before specializing it
to the arithmetic checker. -/
private theorem allTuple
    {p : ℕ → ℕ → ℕ → ℕ → ℕ → Bool} {data : List (ℕ×ℕ×ℕ×ℕ×ℕ)}
    (hall : data.all (fun a => p a.1 a.2.1 a.2.2.1 a.2.2.2.1 a.2.2.2.2) = true)
    {A B V E u : ℕ} (ha : (A,B,V,E,u) ∈ data) : p A B V E u = true :=
  (List.all_eq_true (l := data)
    (p := fun a => p a.1 a.2.1 a.2.2.1 a.2.2.2.1 a.2.2.2.2)).mp
    hall (A,B,V,E,u) ha

theorem boundOfChecks (L : ℕ) {data : List (ℕ×ℕ×ℕ×ℕ×ℕ)}
    (hall : data.all (fun a => LightCeil209.Check a.1 a.2.1 a.2.2.1 a.2.2.2.1 L a.2.2.2.2) = true)
    {A B V E u : ℕ} (ha : (A,B,V,E,u) ∈ data) :
    LightAnalytic209.Alpha A B V E L ≤ (u : ℝ)/(Grid : ℝ) :=
  LightCeil209.check_sound (A := A) (B := B) (V := V) (E := E) (L := L) (u := u)
    (allTuple (p := fun A B V E u => LightCeil209.Check A B V E L u)
      (data := data) (A := A) (B := B) (V := V) (E := E) (u := u) hall ha)

#print axioms checkAllFast_sound
#print axioms boundOfChecks
end JSP233.LightCeilFast209
