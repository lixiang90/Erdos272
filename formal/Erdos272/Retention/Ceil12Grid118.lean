module

public import Erdos272.Retention.JointFringe44
public import Mathlib.Order.Interval.Finset.Nat
public import Mathlib.Algebra.BigOperators.Intervals

@[expose] public section

/-! Actual ceil-grid preceding anchors, with the real interval as the off pool. -/
namespace JSP233.Ceil12Grid118
open StarCompletion APGeometry ThinFringe33 KKRetention32 Restore33
open scoped Classical BigOperators
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 20000

abbrev Key := JointFringe44.Key
def Keys : Finset Key :=
  (Finset.Icc 1 11).sigma (fun d=>(Finset.Icc 1 d).product (Finset.Icc 1 (11/d)))
def ShortKeys : Finset (Σ _d:ℕ,ℕ) :=
  (Finset.Icc 1 11).sigma (fun d=>Finset.Icc 1 (11/d))
def Origin (N : ℕ) (k : Key) : ℤ :=
  (k.2.1:ℤ)+((k.2.2:ℤ)*((N+11)/12:ℕ)-1)*(k.1:ℤ)
def HasAnchor (N : ℕ) (L R : ℤ) (k : Key) (S : Finset ℤ) : Prop :=
  APAt (k.1:ℤ) (Origin N k) (S∩Finset.Icc L R) ∧
    Origin N k∈S∩Finset.Icc L R ∧ Origin N k+(k.1:ℤ)∈S∩Finset.Icc L R

theorem short_keys_card : ShortKeys.card=29 := by
  norm_num [ShortKeys,Finset.card_sigma,Finset.sum_Icc_succ_top]

theorem grid_anchor_cover (N a b d m : ℕ) (hN : 144≤N)
    (ha : 1≤a) (hb : b≤N) (hd : 1≤d) (hdr : d≤11)
    (hspan : b=a+d*(m-1)) (hm : N/12+1<m) :
    ∃k∈Keys,k.1=d ∧ (a:ℤ)≤Origin N k ∧ Origin N k+(d:ℤ)≤b ∧
      (d:ℤ)∣Origin N k-(a:ℤ) := by
  let q := (N+11)/12
  have hq : 0<q := by dsimp only [q];omega
  have hqN : N≤12*q := by dsimp only [q];omega
  have hqm : q≤m-1 := by dsimp only [q];omega
  let rho := (a-1)%d+1
  let z := (a-1)/d
  let j := z/q+1
  have hr : 1≤rho ∧ rho≤d := by
    have hh := Nat.mod_lt (a-1) (by omega : 0<d)
    dsimp only [rho];omega
  have haz : a=rho+d*z := by
    have hh := Nat.mod_add_div (a-1) d
    dsimp only [rho,z];omega
  have hj : z<j*q ∧ j*q≤z+q := by
    have hh := Nat.mod_add_div z q
    have hl := Nat.mod_lt z hq
    dsimp only [j]
    constructor <;> nlinarith [Nat.zero_le (z%q)]
  let u := rho+j*q*d
  have hau : a+d≤u := by dsimp only [u];nlinarith
  have hub : u≤b := by dsimp only [u];nlinarith
  have hjd : j*d≤11 := by
    by_contra hn
    have hh := Nat.mul_le_mul_left q (show 12≤j*d by omega)
    dsimp only [u] at hub
    nlinarith
  have hjlo : 1≤j := Nat.le_add_left 1 (z/q)
  have hjhi : j≤11/d := (Nat.le_div_iff_mul_le (by omega : 0<d)).mpr hjd
  let k : Key := ⟨d,rho,j⟩
  have hk : k∈Keys := Finset.mem_sigma.mpr ⟨Finset.mem_Icc.mpr ⟨hd,hdr⟩,
    Finset.mem_product.mpr ⟨Finset.mem_Icc.mpr hr,Finset.mem_Icc.mpr ⟨hjlo,hjhi⟩⟩⟩
  have hpoint : Origin N k=(u:ℤ)-(d:ℤ) := by
    dsimp only [Origin,k,u,q]
    push_cast
    ring
  refine ⟨k,hk,rfl,?_,?_,?_⟩
  · rw [hpoint]
    have hh : (a:ℤ)+(d:ℤ)≤(u:ℤ) := by exact_mod_cast hau
    omega
  · rw [hpoint];omega
  · rw [hpoint]
    refine ⟨((j*q:ℕ):ℤ)-(z:ℤ)-1,?_⟩
    have haZ : (a:ℤ)=(rho:ℤ)+(d:ℤ)*(z:ℤ) := by exact_mod_cast haz
    dsimp only [u]
    push_cast
    nlinarith only [haZ]

theorem residue_dvd {N : ℕ} {k : Key} {y : ℤ}
    (h : (k.1:ℤ)∣y-Origin N k) : (k.1:ℤ)∣y-(k.2.1:ℤ) := by
  have hg : (k.1:ℤ)∣Origin N k-(k.2.1:ℤ) := by
    refine ⟨(k.2.2:ℤ)*((N+11)/12:ℕ)-1,?_⟩
    dsimp only [Origin]
    ring
  have hh := Int.dvd_add h hg
  convert hh using 1
  ring


#print axioms short_keys_card
#print axioms grid_anchor_cover
#print axioms residue_dvd
end
end JSP233.Ceil12Grid118
