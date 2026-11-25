module

public import Erdos272.Resources.N80470.APLayerSum80470
public import Erdos272.Counting.N80470.AP128Constants80470

@[expose] public section

namespace JSP233.APLossAggregate80470
open APLayerAlgebra80470 APLayerSum80470 APQuotient80470
open AP128Family80470 AP128Constants80470 HarmonicAbel29
open scoped Classical BigOperators
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option maxRecDepth 3000

def Base (n d : ℕ) : ℝ := (n : ℝ)^2/(4*(d : ℝ)^2)+(n : ℝ)/d
def Loss (n d : ℕ) : ℝ := Base n d-(Cost n d : ℝ)
def Credit (n k : ℕ) : ℝ := (n : ℝ)*Coefficient k-Fee k

theorem quarter_floor (k : ℕ) :
    (((k^2/4 : ℕ) : ℝ))=(k : ℝ)^2/4-((k%2 : ℕ) : ℝ)/4 := by
  let t := k/2
  have hsplit : k=2*t+k%2 := by
    have hh := Nat.mod_add_div k 2
    dsimp only [t]
    omega
  have hrem : k%2=0 ∨ k%2=1 := by have hh := Nat.mod_lt k (by decide : 0<2); omega
  rcases hrem with hr | hr
  all_goals
    have he : k^2=4*(t^2+t*(k%2))+k%2 := by
      calc
        _ = (2*t+k%2)^2 := congrArg (fun x : ℕ => x^2) hsplit
        _ = _ := by rw [hr]; ring
    have hf : k^2/4=t^2+t*(k%2) := Nat.div_eq_of_lt_le
      (by rw [he, hr]; nlinarith)
      (by rw [he, hr]; nlinarith)
    have heR : (k : ℝ)^2=4*((t^2+t*(k%2) : ℕ) : ℝ)+((k%2 : ℕ) : ℝ) := by
      exact_mod_cast he
    rw [hf]
    nlinarith only [heR]

theorem loss_identity (n d : ℕ) :
    Loss n d=(((n : ℝ)/d)^2-((n/d : ℕ) : ℝ)^2)/4+
      ((n : ℝ)/d-((n/d : ℕ) : ℝ))+(((n/d)%2 : ℕ) : ℝ)/4 := by
  unfold Loss Base Cost
  rw [Nat.cast_add, quarter_floor]
  ring

theorem loss_nonnegative (n : ℕ) {d : ℕ} (hd : 0<d) : 0≤Loss n d := by
  have hdiv := (nat_div_bounds n d hd).1
  have hq0 : (0 : ℝ)≤((n/d : ℕ) : ℝ) := Nat.cast_nonneg _
  have ht0 : (0 : ℝ)≤(n : ℝ)/d := by positivity
  have hsquare := mul_le_mul hdiv hdiv hq0 ht0
  have hrem : (0 : ℝ)≤(((n/d)%2 : ℕ) : ℝ) := Nat.cast_nonneg _
  rw [loss_identity]
  nlinarith only [hdiv, hsquare, hrem]

theorem layer_credit {n k : ℕ} (hk : 1≤k) (hn : k*(k+1)≤n) :
    Credit n k≤∑ d∈Layer n k, Loss n d := by
  have hs := square_loss hk hn
  have hl := linear_loss hk hn
  have hm := (layer_bounds hk hn).1
  have hp := mul_le_mul_of_nonneg_left hm
    (show 0≤((k%2 : ℕ) : ℝ)/4 by positivity)
  have hsplit : (∑ d∈Layer n k, Loss n d)=
      (∑ d∈Layer n k, (((n : ℝ)/d)^2-(k : ℝ)^2))/4+
      (∑ d∈Layer n k, ((n : ℝ)/d-k))+
      ((k%2 : ℕ) : ℝ)/4*((Layer n k).card : ℝ) := by
    calc
      _ = ∑ d∈Layer n k,
          ((((n : ℝ)/d)^2-(k : ℝ)^2)/4+((n : ℝ)/d-k)+((k%2 : ℕ) : ℝ)/4) := by
        apply Finset.sum_congr rfl
        intro d hd
        rw [loss_identity, layer_quotient hk hd]
      _ = _ := by
        rw [Finset.sum_add_distrib, Finset.sum_add_distrib, Finset.sum_div]
        simp only [Finset.sum_const, nsmul_eq_mul]
        ring
  have hk0 : (0 : ℝ)<k := by exact_mod_cast (show 0<k by omega)
  have he : Credit n k=((n : ℝ)/(k+1)-(3*k+1))/4+
      ((n : ℝ)/(2*((k : ℝ)+1)^2)-1)+
      ((k%2 : ℕ) : ℝ)/4*((n : ℝ)/((k : ℝ)*(k+1))-1) := by
    unfold Credit Coefficient Fee
    field_simp [hk0.ne', (show (k : ℝ)+1≠0 by positivity)]
    <;> ring
  rw [he, hsplit]
  linarith only [hs, hl, hp]

theorem layers_disjoint (n : ℕ) :
    Set.PairwiseDisjoint (↑(Finset.Icc 1 128) : Set ℕ) (Layer n) := by
  intro i hi j hj hij
  apply Finset.disjoint_left.mpr
  intro d hdi hdj
  have hqi := layer_quotient (Finset.mem_Icc.mp hi).1 hdi
  have hqj := layer_quotient (Finset.mem_Icc.mp hj).1 hdj
  exact hij (hqi.symm.trans hqj)

theorem layers_inside {n : ℕ} (hn : 16512≤n) :
    (Finset.Icc 1 128).biUnion (Layer n)⊆Finset.Icc 2 n := by
  intro d hd
  obtain ⟨k, hk, hdk⟩ := Finset.mem_biUnion.mp hd
  obtain ⟨hk1, hk128⟩ := Finset.mem_Icc.mp hk
  have hnk : k*(k+1)≤n := by
    have hp := Nat.mul_le_mul hk128 (Nat.add_le_add_right hk128 1)
    omega
  have hsmall : k+1≤n := by
    have hp := Nat.mul_le_mul hk1 (Nat.le_refl (k+1))
    have hprod : k+1≤k*(k+1) := by simpa only [one_mul] using hp
    exact hprod.trans hnk
  have hleft : 1≤n/(k+1) :=
    (Nat.le_div_iff_mul_le (by omega : 0<k+1)).mpr (by simpa using hsmall)
  obtain ⟨hdl, hdr⟩ := Finset.mem_Icc.mp hdk
  refine Finset.mem_Icc.mpr ⟨?_, ?_⟩
  · dsimp only [Left] at hdl
    omega
  · exact hdr.trans (Nat.div_le_self n k)

theorem selected_loss {n : ℕ} (hn : 16512≤n) :
    (∑ k∈Finset.Icc 1 128, Credit n k)≤∑ d∈Finset.Icc 2 n, Loss n d := by
  calc
    _ ≤ ∑ k∈Finset.Icc 1 128, ∑ d∈Layer n k, Loss n d := by
      apply Finset.sum_le_sum
      intro k hk
      obtain ⟨hk1, hk128⟩ := Finset.mem_Icc.mp hk
      have hp := Nat.mul_le_mul hk128 (Nat.add_le_add_right hk128 1)
      exact layer_credit hk1 (by omega : k*(k+1)≤n)
    _ = ∑ d∈(Finset.Icc 1 128).biUnion (Layer n), Loss n d :=
      (Finset.sum_biUnion (layers_disjoint n)).symm
    _ ≤ _ := Finset.sum_le_sum_of_subset_of_nonneg (layers_inside hn) (by
      intro d hd _
      exact loss_nonnegative n (by have hh := (Finset.mem_Icc.mp hd).1; omega))

theorem half_integer_tail {n : ℕ} (hn : 64≤n) :
    (∑ d∈Finset.Icc 65 n, (1 : ℝ)/(d : ℝ)^2)≤2/129-2/(2*(n : ℝ)+1) := by
  by_cases h65 : 65≤n
  · have hp := Finset.sum_le_sum (s := Finset.Icc 65 n) (fun d hd =>
      half_integer_upper (d := (d : ℝ))
        (by exact_mod_cast (show 1≤d by have hh := (Finset.mem_Icc.mp hd).1; omega)))
    let f : ℕ→ℝ := fun d => 2/(2*(d : ℝ)-1)
    have hf : ∀ d : ℕ, f (d+1)=2/(2*(d : ℝ)+1) := by
      intro d
      dsimp only [f]
      congr 1
      push_cast
      ring
    have ht := sum_consecutive f h65
    have he : (∑ d∈Finset.Icc 65 n,
        (2/(2*(d : ℝ)-1)-2/(2*(d : ℝ)+1)))=2/129-2/(2*(n : ℝ)+1) := by
      calc
        _ = ∑ d∈Finset.Icc 65 n, (f d-f (d+1)) := by simp only [hf, f]
        _ = f 65-f (n+1) := ht
        _ = _ := by rw [hf n]; norm_num [f]
    rw [he] at hp
    exact hp
  · have he : n=64 := by omega
    subst n
    norm_num

theorem square_sum_bound {n : ℕ} (hn : 64≤n) :
    (∑ d∈Finset.Icc 2 n, (1 : ℝ)/(d : ℝ)^2)≤4*Kappa-2/(2*(n : ℝ)+1) := by
  have hsplit : Finset.Icc 2 n=Finset.Icc 2 64∪Finset.Icc 65 n := by
    ext d
    simp only [Finset.mem_Icc, Finset.mem_union]
    omega
  have hdis : Disjoint (Finset.Icc 2 64) (Finset.Icc 65 n) := by
    apply Finset.disjoint_left.mpr
    intro d h1 h2
    simp only [Finset.mem_Icc] at h1 h2
    omega
  have hfirst : (∑ d∈(Finset.Icc 1 64 : Finset ℕ), (1 : ℝ)/(d : ℝ)^2)=
      1+∑ d∈(Finset.Icc 2 64 : Finset ℕ), (1 : ℝ)/(d : ℝ)^2 := by
    have hi : Finset.Icc 1 64=insert 1 (Finset.Icc 2 64) := by ext d; simp; omega
    rw [hi, Finset.sum_insert (by simp)]
    norm_num
  have hc := AP128Constants80470.square_coefficient
  rw [hfirst] at hc
  have ht := half_integer_tail hn
  rw [hsplit, Finset.sum_union hdis]
  linarith only [hc, ht]

theorem base_sum_bound {n : ℕ} (hn : 64≤n) :
    (∑ d∈Finset.Icc 2 n, Base n d)≤
      Kappa*(n : ℝ)^2+(n : ℝ)*(Harmonic n-1)-(n : ℝ)/4+1/8 := by
  have hs := square_sum_bound hn
  have hquad := mul_le_mul_of_nonneg_left hs
    (show 0≤(n : ℝ)^2/4 by positivity)
  have hterm : ∀ d : ℕ, Base n d=(n : ℝ)^2/4*(1/(d : ℝ)^2)+(n : ℝ)*(1/d) := by
    intro d
    unfold Base
    ring
  have hid : (∑ d∈Finset.Icc 2 n, Base n d)=
      (n : ℝ)^2/4*(∑ d∈Finset.Icc 2 n, (1 : ℝ)/(d : ℝ)^2)+
      (n : ℝ)*(Harmonic n-1) := by
    simp_rw [hterm]
    rw [Finset.sum_add_distrib, ←Finset.mul_sum, ←Finset.mul_sum,
      APTail208.harmonic_tail_two (by omega : 1≤n)]
  have hp : (n : ℝ)/4-1/8≤(n : ℝ)^2/(2*(2*(n : ℝ)+1)) := by
    apply (le_div_iff₀ (by positivity : 0<2*(2*(n : ℝ)+1))).mpr
    nlinarith
  have he : (n : ℝ)^2/4*(4*Kappa-2/(2*(n : ℝ)+1))=
      Kappa*(n : ℝ)^2-(n : ℝ)^2/(2*(2*(n : ℝ)+1)) := by
    field_simp [show 2*(n : ℝ)+1≠0 by positivity]
    <;> ring
  rw [he] at hquad
  rw [hid]
  linarith only [hquad, hp]

#print axioms quarter_floor
#print axioms loss_identity
#print axioms loss_nonnegative
#print axioms layer_credit
#print axioms layers_disjoint
#print axioms layers_inside
#print axioms selected_loss
#print axioms half_integer_tail
#print axioms square_sum_bound
#print axioms base_sum_bound
end
end JSP233.APLossAggregate80470
