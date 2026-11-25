module

public import Mathlib.Algebra.Order.Field.Rat
public import Erdos272.Foundation.ProofTactics

@[expose] public section
namespace JSP233.PairError20258
set_option autoImplicit false

def primes : List ℕ := [2,3,5,7,11,13,17,19,23,29,31,37,41,43,47,53,59,61]
def steps : List ℕ := 1::primes

def reciprocal (p : ℕ) : ℚ := 1/(p : ℚ)^2

/-- Sum over unordered pairs, counted once in the list order. -/
def pairs : List ℕ → ℚ
  | [] => 0
  | p::ps => reciprocal p*(ps.map reciprocal).sum+pairs ps

def weight (d : ℕ) : ℚ := (3/2)*pairs (primes.filter (fun p => d < p))
def coefficient (ds : List ℕ) (j : ℕ) : ℚ := (ds.map (fun d => weight d/(d : ℚ)^j)).sum
def fee (ds : List ℕ) (n : ℚ) : ℚ := (ds.map (fun d => weight d*(1+n/(d : ℚ))^2)).sum

private theorem expand (ds : List ℕ) (n : ℚ) :
    fee ds n=coefficient ds 0+2*coefficient ds 1*n+coefficient ds 2*n^2 := by
  induction ds with
  | nil => simp [fee,coefficient]
  | cons d ds ih =>
    change weight d*(1+n/(d : ℚ))^2+fee ds n =
      (weight d/(d : ℚ)^0+coefficient ds 0)+2*(weight d/(d : ℚ)^1+coefficient ds 1)*n+
        (weight d/(d : ℚ)^2+coefficient ds 2)*n^2
    rw [ih]
    simp only [pow_zero,pow_one,div_eq_mul_inv]
    ring

private theorem three_coefficients :
    coefficient steps 0 ≤ 120/1000 ∧ 2*coefficient steps 1 ≤ 210/1000 ∧
      coefficient steps 2 ≤ 99/1000 := by decide +kernel

/-- The same three small integer coefficients pay all 969 paired-modulus
errors, for every ground size. -/
theorem uniform (n : ℚ) (hn : 0 ≤ n) : fee steps n ≤ (99*n^2+210*n+120)/1000 := by
  obtain ⟨a,b,c⟩ := three_coefficients
  rw [expand]
  linarith only [a,mul_le_mul_of_nonneg_right b hn,mul_le_mul_of_nonneg_right c (sq_nonneg n)]

#print axioms uniform
end JSP233.PairError20258
