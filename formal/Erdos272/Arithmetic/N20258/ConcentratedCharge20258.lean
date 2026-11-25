module

public import Erdos272.Capacity.N20258.ConcentratedPrice20258

@[expose] public section
namespace JSP233.ConcentratedCharge20258
open StarCompletion ConcentratedPopulation20258 ConcentratedPrice20258
open scoped BigOperators
set_option autoImplicit false

/-- The span tests count two initial intervals of strides. A single
member-size cap gives a closed upper bound using four integer divisions. -/
def simple (n a k top : ℕ) :=
  (n+4*k*(k+1)*top+k*k*(n/(a+1)+1))*((n-1)/a+(n-1)/(2*a-min k (a/2)))

def debt (p : Plan) (n : ℕ) :=
  ((rows p).map (fun (k,w) => w*simple n (p.minimum-1-k) k p.top)).sum

theorem budget_le {n a k top : ℕ} (pos : 0<a) (ground : 0<n) : budget n a k top≤simple n a k top := by
  let D := Finset.Icc 1 ((n-1)/a)
  let b := 2*a-min k (a/2)
  have sb : a≤b := by dsimp only [b]; have := min_le_right k (a/2); omega
  have bp : 0<b := pos.trans_le sb
  have gates (t : ℕ) (ht : a≤t) : (∑ d∈D, if d*t<n then 1 else 0)=(n-1)/t := by
    have positive := pos.trans_le ht
    have sub : (n-1)/t≤(n-1)/a := Nat.div_le_div_left ht pos
    have eqn : D.filter (fun d => d*t<n)=Finset.Icc 1 ((n-1)/t) := by
      ext d
      simp only [D,Finset.mem_filter,Finset.mem_Icc,Nat.le_div_iff_mul_le positive]
      constructor
      · rintro ⟨⟨lo,_⟩,size⟩; exact ⟨lo,by omega⟩
      · rintro ⟨lo,size⟩; exact ⟨⟨lo,((Nat.le_div_iff_mul_le positive).mpr size).trans sub⟩,by omega⟩
    simp only [Finset.sum_boole,eqn,Nat.card_Icc,Nat.add_sub_cancel,Nat.cast_id]
  have count : ∑ d∈D,occupancy n a k d=(n-1)/a+(n-1)/b := by
    unfold occupancy
    rw [Finset.sum_add_distrib,gates a le_rfl,gates b sb]
  let C := n+4*k*(k+1)*top+k*k*(n/(a+1)+1)
  have unit : n≤(n/(a+1)+1)*(a+1) := by
    simpa only [Nat.mul_comm] using (Nat.lt_mul_div_succ n (Nat.succ_pos a)).le
  have per (d : ℕ) : perStride n a k top d≤C*occupancy n a k d := by
    let o := occupancy n a k d
    have amount : n*o/(a+1)≤(n/(a+1)+1)*o := by
      have h := Nat.mul_le_mul_right o unit
      calc
        _ ≤ (((n/(a+1)+1)*o)*(a+1))/(a+1) := Nat.div_le_div_right (by nlinarith only [h])
        _ = _ := Nat.mul_div_cancel _ (Nat.succ_pos a)
    have size := min_le_left top ((n-1)/d+1+k)
    have weighted := Nat.mul_le_mul_right (4*k*(k+1)*o) size
    have exterior := Nat.mul_le_mul_left (k*k) amount
    change n*o+k*(2*(k+1)*(2*min top ((n-1)/d+1+k)*o)+k*(n*o/(a+1)))≤C*o
    dsimp only [C]
    nlinarith only [weighted,exterior]
  calc
    _ ≤ ∑ d∈D,C*occupancy n a k d := Finset.sum_le_sum (fun d _ => per d)
    _ = _ := by rw [←Finset.mul_sum,count]; rfl

theorem family {n : ℕ} {A : Finset (Finset ℤ)} {p : Plan} (valid : p.Valid)
    (legal : Legal (Ground n) A) (pos : 0<n) (cap : n≤2^18)
    (large : ∀ S∈A,p.minimum≤S.card) (bad : ∀ S∈A,¬IsAP S) :
    p.head*A.card≤(∑ S∈A,(IntrinsicTriples208.Pool S).card)+debt p n := by
  apply (ConcentratedPrice20258.family valid legal cap large bad).trans
  apply Nat.add_le_add_left
  unfold debt fee
  have steps := valid.2.2.2.2.2.2.2.2.1
  generalize eqn : rows p=r at steps ⊢
  clear eqn
  induction r with
  | nil => exact le_rfl
  | cons t r ih =>
    obtain ⟨k,w⟩ := t
    have h := steps (k,w) (List.mem_cons_self ..)
    change k+2≤p.minimum at h
    exact Nat.add_le_add (Nat.mul_le_mul_left w (budget_le (by omega) pos))
      (ih (fun t ht => steps t (List.mem_cons_of_mem _ ht)))

#print axioms family
end JSP233.ConcentratedCharge20258
