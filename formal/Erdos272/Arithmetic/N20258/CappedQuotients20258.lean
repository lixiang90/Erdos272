module

public import Erdos272.Arithmetic.N20258.ConcentratedCharge20258

@[expose] public section
namespace JSP233.CappedQuotients20258
open scoped Classical BigOperators
set_option autoImplicit false

def quotientSum (w v : ℕ) := ∑ j∈Finset.Icc 1 v,w/j

def capped (w D top k : ℕ) :=
  if D=0 then 0 else
  let b := top-1-k
  let z := min b (w/D)
  (k+1+z)*D+quotientSum w b-quotientSum w z

private theorem indicator (w b d : ℕ) (hd : 0<d) :
    (∑ j∈Finset.Icc 1 b,if j*d≤w then 1 else 0)=min b (w/d) := by
  have eq : (Finset.Icc 1 b).filter (fun j => j*d≤w)=Finset.Icc 1 (min b (w/d)) := by
    ext j
    simp only [Finset.mem_filter,Finset.mem_Icc,le_min_iff,Nat.le_div_iff_mul_le hd,and_assoc]
  simp only [Finset.sum_boole,eq,Nat.card_Icc,Nat.add_sub_cancel,Nat.cast_id]

/-- Both orders of summation count (d,j) with d*j≤w in the same rectangle. -/
theorem swap (w D b : ℕ) : (∑ d∈Finset.Icc 1 D,min b (w/d))=∑ j∈Finset.Icc 1 b,min D (w/j) := by
  calc
    _ = ∑ d∈Finset.Icc 1 D, ∑ j∈Finset.Icc 1 b,if j*d≤w then 1 else 0 :=
      Finset.sum_congr rfl (fun d hd => (indicator w b d (Finset.mem_Icc.mp hd).1).symm)
    _ = ∑ j∈Finset.Icc 1 b, ∑ d∈Finset.Icc 1 D,if j*d≤w then 1 else 0 := Finset.sum_comm
    _ = _ := Finset.sum_congr rfl (fun j hj => by
      simpa only [Nat.mul_comm j] using indicator w D j (Finset.mem_Icc.mp hj).1)

private theorem trim (w D b : ℕ) (pos : 0<D) :
    (∑ j∈Finset.Icc 1 b,min D (w/j))+quotientSum w (min b (w/D))=min b (w/D)*D+quotientSum w b := by
  let A := Finset.Icc 1 b
  let z := min b (w/D)
  have eq : A.filter (fun j => j≤z)=Finset.Icc 1 z := by
    ext j
    simp only [A,Finset.mem_filter,Finset.mem_Icc]
    have zb : z≤b := min_le_left ..
    omega
  have low : ∑ j∈A.filter (fun j => j≤z),min D (w/j)=z*D := by
    rw [eq]
    calc
      _ = ∑ _j∈Finset.Icc 1 z,D := Finset.sum_congr rfl (fun j hj => by
        obtain ⟨jp,range⟩ := Finset.mem_Icc.mp hj
        have bound := (Nat.le_div_iff_mul_le pos).mp (range.trans (min_le_right ..))
        exact min_eq_left ((Nat.le_div_iff_mul_le jp).mpr (by simpa only [Nat.mul_comm D] using bound)))
      _ = _ := by simp
  have high : ∑ j∈A.filter (fun j => ¬j≤z),min D (w/j)=∑ j∈A.filter (fun j => ¬j≤z),w/j := by
    apply Finset.sum_congr rfl
    intro j hj
    obtain ⟨mem,gt⟩ := Finset.mem_filter.mp hj
    obtain ⟨jp,jb⟩ := Finset.mem_Icc.mp mem
    have no : ¬j≤w/D := fun le => gt (le_min jb le)
    have mult : ¬j*D≤w := fun le => no ((Nat.le_div_iff_mul_le pos).mpr le)
    exact min_eq_right (by
      by_contra! less
      exact mult (by simpa only [Nat.mul_comm j] using (Nat.le_div_iff_mul_le jp).mp less.le))
  have lhs := Finset.sum_filter_add_sum_filter_not A (fun j => j≤z) (fun j => min D (w/j))
  have rhs := Finset.sum_filter_add_sum_filter_not A (fun j => j≤z) (fun j => w/j)
  rw [low,high] at lhs
  rw [eq] at rhs
  change (∑ j∈A,min D (w/j))+(∑ j∈Finset.Icc 1 z,w/j)=z*D+∑ j∈A,w/j
  rw [←lhs,←rhs]
  ac_rfl

theorem sum_sizes {w D top k : ℕ} (cap : k+1≤top) :
    (∑ d∈Finset.Icc 1 D,min top (w/d+1+k))=capped w D top k := by
  by_cases empty : D=0
  · simp [empty,capped]
  let b := top-1-k
  let z := min b (w/D)
  have each (d : ℕ) : min top (w/d+1+k)=(k+1)+min b (w/d) := by dsimp only [b]; omega
  simp only [each,Finset.sum_add_distrib,Finset.sum_const,smul_eq_mul,Nat.card_Icc,Nat.add_sub_cancel,swap]
  have balanced := trim w D b (by omega)
  change (∑ j∈Finset.Icc 1 b,min D (w/j))+quotientSum w z=z*D+quotientSum w b at balanced
  change _=capped w D top k
  simp only [capped,ite_eq_right empty]
  rw [←Nat.mul_add D k 1]
  change D*(k+1)+_=(k+1+z)*D+quotientSum w b-quotientSum w z
  rw [Nat.add_mul,Nat.mul_comm (k+1) D]
  omega

#print axioms sum_sizes
end JSP233.CappedQuotients20258
