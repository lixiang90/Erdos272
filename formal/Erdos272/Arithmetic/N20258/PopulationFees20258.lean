module

public import Erdos272.Arithmetic.N20258.TwoStrideCharges20258

@[expose] public section
namespace JSP233.PopulationFees20258
open CappedQuotients20258 TwoStrideCharges20258 PopulationTariff20258
set_option autoImplicit false

structure Prefix (w : ℕ) where
  get : ℕ → ℕ
  correct : ∀ j,get j=quotientSum w j

private theorem succ_sum (w j : ℕ) : quotientSum w (j+1)=quotientSum w j+w/(j+1) := by
  exact Finset.sum_Icc_succ_top (by omega : 1≤j+1) (fun k => w/k)

def consecutive (w : ℕ) : ℕ → ℕ → List ℕ → Bool
  | _,_,[] => true
  | j,v,x::xs => decide (x=v) && consecutive w (j+1) (x+w/(j+1)) xs

private theorem read {w : ℕ} (xs : List ℕ) {j acc : ℕ} (ok : consecutive w j acc xs=true)
    (start : acc=quotientSum w j) (i x : ℕ) (h : xs[i]?=some x) : x=quotientSum w (j+i) := by
  induction xs generalizing j acc i with
  | nil => simp at h
  | cons y ys ih =>
    simp only [consecutive,Bool.and_eq_true,decide_eq_true_eq] at ok
    obtain ⟨eq,next⟩ := ok
    cases i with
    | zero => simp only [List.getElem?_cons_zero,Option.some.injEq] at h; simpa only [←h,Nat.add_zero] using eq.trans start
    | succ i =>
      have entry := ih next (by rw [eq,start,succ_sum]) i (by simpa using h)
      simpa only [Nat.add_assoc,Nat.add_comm 1 i] using entry

/-- A single checked row of successive integer divisions serves every
mark, size and population level on the same physical ground. -/
def prefixTable (w : ℕ) (xs : List ℕ) (ok : consecutive w 0 0 xs=true) : Prefix w where
  get j := xs[j]?.getD (quotientSum w j)
  correct j := by
    cases h : xs[j]? with
    | none => rfl
    | some x =>
      change x=quotientSum w j
      simpa only [Nat.zero_add] using read xs ok (by simp [quotientSum]) j x h

def partialSums (w j acc : ℕ) : ℕ → List ℕ
  | 0 => [acc]
  | k+1 => acc::partialSums w (j+1) (acc+w/(j+1)) k

theorem partialSums_ok (w k j acc : ℕ) : consecutive w j acc (partialSums w j acc k)=true := by
  induction k generalizing j acc with
  | zero => simp [partialSums,consecutive]
  | succ k ih => simp only [partialSums,consecutive,decide_true,Bool.true_and,ih]

def tabulate (w k : ℕ) : Prefix w := prefixTable w (partialSums w 0 0 k) (partialSums_ok w k 0 0)

def cappedWith {w : ℕ} (p : Prefix w) (D top k : ℕ) :=
  if D=0 then 0 else
  let b := top-1-k
  let z := min b (w/D)
  (k+1+z)*D+p.get b-p.get z

private theorem cappedWith_eq {w : ℕ} (p : Prefix w) (D top k : ℕ) :
    cappedWith p D top k=capped w D top k := by simp only [cappedWith,capped,p.correct]

def fast {n : ℕ} (p : Prefix (n-1)) (a k top : ℕ) :=
  let D := (n-1)/a
  let E := (n-1)/(2*a-min k (a/2))
  let u := n/(a+1)
  let v := 2*n/(a+1)
  n*(D+E)+4*k*(k+1)*(cappedWith p D top k+cappedWith p E top k)+k*k*(D*u+E*(v-u))

def price {n : ℕ} (p : Prefix (n-1)) (t : Test) := match t with
  | .marks l k top false =>
    if 0<n ∧ 0<l-1-k ∧ k+1≤top then fast (n:=n) p (l-1-k) k top else t.cost n
  | _ => t.cost n

private theorem price_eq {n : ℕ} (p : Prefix (n-1)) (t : Test) : price p t=t.cost n := by
  cases t with
  | overlap => rfl
  | marks l k top closed =>
    cases closed with
    | true => rfl
    | false =>
      simp only [price]
      split
      · next h =>
          simp only [Test.cost,Bool.false_eq_true,ite_false,fast,cappedWith_eq]
          exact (exact_charge h.1 h.2.1 h.2.2).symm
      · rfl

def bill {n : ℕ} (p : Prefix (n-1)) (t : Table) := (t.map (fun (r,w) => w*price p r)).sum

theorem bill_eq {n : ℕ} (p : Prefix (n-1)) (t : Table) : bill p t=cost t n := by
  simp only [bill,cost,price_eq]

#print axioms bill_eq
end JSP233.PopulationFees20258
