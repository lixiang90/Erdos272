module

public import Erdos272.Arithmetic.N20258.CappedQuotients20258
public import Erdos272.Counting.N20258.PopulationTariff20258

@[expose] public section
namespace JSP233.TwoStrideCharges20258
open CappedQuotients20258 ConcentratedPopulation20258 PopulationTariff20258
open scoped BigOperators
set_option autoImplicit false

/-- The occupied strides form two initial segments. Their marked-site
contributions are evaluated by summing the sizes across the two segments. -/
def charge (n a k top : ℕ) :=
  let D := (n-1)/a
  let E := (n-1)/(2*a-min k (a/2))
  let u := n/(a+1)
  let v := 2*n/(a+1)
  n*(D+E)+4*k*(k+1)*(capped (n-1) D top k+capped (n-1) E top k)+k*k*(D*u+E*(v-u))

theorem exact_charge {n a k top : ℕ} (ground : 0<n) (pos : 0<a) (cap : k+1≤top) :
    budget n a k top=charge n a k top := by
  let b := 2*a-min k (a/2)
  let D := (n-1)/a
  let E := (n-1)/b
  let u := n/(a+1)
  let v := 2*n/(a+1)
  let S (d : ℕ) := min top ((n-1)/d+1+k)
  let K := 4*k*(k+1)
  let H := k*k
  let f (x d : ℕ) := n+K*S d+H*x
  have ab : a≤b := by dsimp [b]; have := min_le_right k (a/2); omega
  have bp := pos.trans_le ab
  have cover : E≤D := Nat.div_le_div_left ab pos
  have uv : u≤v := Nat.div_le_div_right (show n≤2*n by omega)
  have clip : (Finset.Icc 1 D).filter (fun d => d≤E)=Finset.Icc 1 E := by
    ext d
    simp only [Finset.mem_filter,Finset.mem_Icc]
    omega
  have each (d : ℕ) (mem : d∈Finset.Icc 1 D) :
      perStride n a k top d=f u d+(if d≤E then f (v-u) d else 0) := by
    have step := (Nat.le_div_iff_mul_le pos).mp (Finset.mem_Icc.mp mem).2
    have first : d*a<n := by omega
    have second : d*b<n ↔ d≤E := by
      change d*b<n ↔ d≤(n-1)/b
      rw [Nat.le_div_iff_mul_le bp]
      omega
    have occup : occupancy n a k d=1+(if d≤E then 1 else 0) := by
      change (if d*a<n then 1 else 0)+(if d*b<n then 1 else 0)=_
      simp only [first,ite_true,second]
    change n*occupancy n a k d+k*(2*(k+1)*(2*S d*occupancy n a k d)+k*(n*occupancy n a k d/(a+1)))=_
    rw [occup]
    by_cases early : d≤E
    · simp only [ite_eq_left early]
      change n*2+k*(2*(k+1)*(2*S d*2)+k*(n*2/(a+1)))=_
      rw [Nat.mul_comm n 2]
      change 2*n+k*(2*(k+1)*(2*S d*2)+k*v)=_
      dsimp only [f,K,H]
      have restore : v-u+u=v := Nat.sub_add_cancel uv
      calc
        _ = 2*n+k*(2*(k+1)*(2*S d*2)+k*((v-u)+u)) := by rw [restore]
        _ = _ := by ring
    · simp only [ite_eq_right early,Nat.add_zero,Nat.mul_one]
      dsimp only [f,K,H,u]
      ring
  have group (z x : ℕ) : (∑ d∈Finset.Icc 1 z,f x d)=z*n+K*capped (n-1) z top k+z*(H*x) := by
    simp only [f,Finset.sum_add_distrib,Finset.sum_const,Nat.card_Icc,Nat.add_sub_cancel,smul_eq_mul,
      ←Finset.mul_sum,S,sum_sizes cap]
  calc
    _ = ∑ d∈Finset.Icc 1 D,(f u d+if d≤E then f (v-u) d else 0) := Finset.sum_congr rfl each
    _ = (∑ d∈Finset.Icc 1 D,f u d)+∑ d∈Finset.Icc 1 E,f (v-u) d := by
      rw [Finset.sum_add_distrib,←Finset.sum_filter,clip]
    _ = _ := by
      rw [group,group]
      change D*n+K*capped (n-1) D top k+D*(H*u)+(E*n+K*capped (n-1) E top k+E*(H*(v-u)))=
        n*(D+E)+K*(capped (n-1) D top k+capped (n-1) E top k)+H*(D*u+E*(v-u))
      ring

#print axioms exact_charge
end JSP233.TwoStrideCharges20258
