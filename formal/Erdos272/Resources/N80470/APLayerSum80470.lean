module

public import Erdos272.Resources.N80470.APLayerAlgebra80470
public import Erdos272.Counting.APTail208

@[expose] public section

namespace JSP233.APLayerSum80470
open APLayerAlgebra80470
open scoped BigOperators
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1000000

def Left (n k : ℕ) : ℕ := n/(k+1)+1
def Right (n k : ℕ) : ℕ := n/k
def Layer (n k : ℕ) : Finset ℕ := Finset.Icc (Left n k) (Right n k)

theorem nat_div_bounds (n b : ℕ) (hb : 0<b) :
    ((n/b : ℕ) : ℝ)≤(n : ℝ)/b ∧ (n : ℝ)/b<((n/b : ℕ) : ℝ)+1 := by
  have hbR : (0 : ℝ)<b := by exact_mod_cast hb
  have hm : ((n%b : ℕ) : ℝ)<b := by exact_mod_cast Nat.mod_lt n hb
  have he : ((n%b : ℕ) : ℝ)+(b : ℝ)*((n/b : ℕ) : ℝ)=n := by
    exact_mod_cast Nat.mod_add_div n b
  constructor
  · apply (le_div_iff₀ hbR).mpr
    nlinarith only [he, Nat.cast_nonneg (α := ℝ) (n%b)]
  · apply (div_lt_iff₀ hbR).mpr
    nlinarith only [he, hm]

theorem layer_nonempty {n k : ℕ} (hk : 1≤k) (hn : k*(k+1)≤n) :
    Left n k≤Right n k := by
  have hk0 : 0<k := by omega
  have ht : k≤n/(k+1) := (Nat.le_div_iff_mul_le (by omega : 0<k+1)).mpr hn
  have hp := Nat.div_mul_le_self n (k+1)
  apply (Nat.le_div_iff_mul_le hk0).mpr
  dsimp only [Left]
  nlinarith only [ht, hp]

theorem layer_quotient {n k d : ℕ} (hk : 1≤k) (hd : d∈Layer n k) : n/d=k := by
  obtain ⟨hleft, hright⟩ := Finset.mem_Icc.mp hd
  have hk0 : 0<k := by omega
  have hlo : n<d*(k+1) := (Nat.div_lt_iff_lt_mul (by omega : 0<k+1)).mp
    (by dsimp only [Left] at hleft; omega)
  have hhi : d*k≤n := (Nat.le_div_iff_mul_le hk0).mp hright
  exact Nat.div_eq_of_lt_le (by nlinarith only [hhi]) (by nlinarith only [hlo])

theorem layer_bounds {n k : ℕ} (hk : 1≤k) (hn : k*(k+1)≤n) :
    (n : ℝ)/((k : ℝ)*(k+1))-1≤((Layer n k).card : ℝ) ∧
    (Left n k : ℝ)+Right n k≤(n : ℝ)/k+(n : ℝ)/(k+1)+1 := by
  have hkR : (0 : ℝ)<k := by exact_mod_cast (show 0<k by omega)
  have hk1R : (0 : ℝ)<(k : ℝ)+1 := by positivity
  have hleft := nat_div_bounds n (k+1) (by omega)
  have hright := nat_div_bounds n k (by omega)
  norm_num only [Nat.cast_add, Nat.cast_one] at hleft
  have hlr := layer_nonempty hk hn
  have hcardN : (Layer n k).card+n/(k+1)=n/k := by
    simp only [Layer, Nat.card_Icc, Left, Right] at *
    omega
  have hcard : ((Layer n k).card : ℝ)+((n/(k+1) : ℕ) : ℝ)=((n/k : ℕ) : ℝ) := by
    exact_mod_cast hcardN
  have he : (n : ℝ)/k-(n : ℝ)/(k+1)=(n : ℝ)/((k : ℝ)*(k+1)) := by
    field_simp [hkR.ne', hk1R.ne']
    <;> ring
  constructor
  · rw [←he]
    linarith only [hleft.1, hright.2, hcard]
  · dsimp only [Left, Right]
    push_cast
    linarith only [hleft.1, hright.1]

theorem sum_consecutive (f : ℕ→ℝ) {l r : ℕ} (hlr : l≤r) :
    (∑ d∈Finset.Icc l r, (f d-f (d+1)))=f l-f (r+1) := by
  obtain ⟨m, rfl⟩ := Nat.exists_eq_add_of_le hlr
  induction m with
  | zero => simp
  | succ m ih =>
      rw [show l+(m+1)=(l+m)+1 by omega,
        Finset.sum_Icc_succ_top (by omega : l≤l+m+1), ih (by omega)]
      ring

theorem sum_Icc_cast {l r : ℕ} (hlr : l≤r) :
    (∑ d∈Finset.Icc l r, (d : ℝ))=
      ((Finset.Icc l r).card : ℝ)*((l : ℝ)+r)/2 := by
  have hlength : ∀ m : ℕ,
      2*(∑ d∈Finset.Icc l (l+m), (d : ℝ))=((m : ℝ)+1)*(2*l+m) := by
    intro m
    induction m with
    | zero => simp <;> ring
    | succ m ih =>
        rw [show l+(m+1)=(l+m)+1 by omega,
          Finset.sum_Icc_succ_top (by omega : l≤l+m+1)]
        push_cast
        nlinarith only [ih]
  obtain ⟨m, rfl⟩ := Nat.exists_eq_add_of_le hlr
  have hcard : (Finset.Icc l (l+m)).card=m+1 := by simp only [Nat.card_Icc]; omega
  rw [hcard]
  push_cast
  nlinarith only [hlength m]

theorem square_loss {n k : ℕ} (hk : 1≤k) (hn : k*(k+1)≤n) :
    (n : ℝ)/(k+1)-(3*k+1)≤
      ∑ d∈Layer n k, (((n : ℝ)/d)^2-(k : ℝ)^2) := by
  have hlr := layer_nonempty hk hn
  have hl : 0<Left n k := Nat.zero_lt_succ _
  have hkR : (1 : ℝ)≤k := by exact_mod_cast hk
  have hnR : (k : ℝ)*(k+1)≤n := by exact_mod_cast hn
  have hleft := nat_div_bounds n (k+1) (by omega)
  have hright := nat_div_bounds n k (by omega)
  norm_num only [Nat.cast_add, Nat.cast_one] at hleft
  have hlb : (Left n k : ℝ)≤(n : ℝ)/(k+1)+1 := by
    dsimp only [Left]
    push_cast
    linarith only [hleft.1]
  have htl : (n : ℝ)/k≤((Right n k+1 : ℕ) : ℝ) := by
    dsimp only [Right]
    push_cast
    linarith only [hright.2]
  have htu : ((Right n k+1 : ℕ) : ℝ)≤(n : ℝ)/k+1 := by
    dsimp only [Right]
    push_cast
    linarith only [hright.1]
  have hend := square_endpoint hkR hnR (by exact_mod_cast hl) hlb htl htu
  have hpoint : ∀ d∈Layer n k,
      (n : ℝ)^2*(1/(d : ℝ)-1/((d : ℝ)+1))-(k : ℝ)^2≤
        ((n : ℝ)/d)^2-(k : ℝ)^2 := by
    intro d hd
    have hdN : 0<d := hl.trans_le (Finset.mem_Icc.mp hd).1
    have hdR : (0 : ℝ)<d := by exact_mod_cast hdN
    have hp := mul_le_mul_of_nonneg_left (reciprocal_square_lower hdR) (sq_nonneg (n : ℝ))
    have he : (1 : ℝ)/(d*((d : ℝ)+1))=1/(d : ℝ)-1/((d : ℝ)+1) := by
      field_simp [hdR.ne', (show (d : ℝ)+1≠0 by positivity)]
      <;> ring
    rw [he] at hp
    have heq : (n : ℝ)^2*(1/(d : ℝ)^2)=((n : ℝ)/d)^2 := by
      rw [div_pow]
      ring
    rw [heq] at hp
    exact sub_le_sub_right hp _
  have hsum := Finset.sum_le_sum hpoint
  have htel := sum_consecutive (fun d => 1/(d : ℝ)) hlr
  have hcard : ((Layer n k).card : ℝ)=((Right n k+1 : ℕ) : ℝ)-(Left n k : ℝ) := by
    simp only [Layer, Nat.card_Icc]
    rw [Nat.cast_sub (by omega : Left n k≤Right n k+1)]
  have he : (∑ d∈Layer n k,
      ((n : ℝ)^2*(1/(d : ℝ)-1/((d : ℝ)+1))-(k : ℝ)^2))=
      F n k (Left n k)-F n k ((Right n k+1 : ℕ) : ℝ) := by
    rw [Finset.sum_sub_distrib, ←Finset.mul_sum]
    simp only [Finset.sum_const, nsmul_eq_mul]
    have hh : (∑ d∈Layer n k, (1/(d : ℝ)-1/((d : ℝ)+1)))=
        1/(Left n k : ℝ)-1/((Right n k+1 : ℕ) : ℝ) := by
      simpa only [Layer, Nat.cast_add, Nat.cast_one] using htel
    rw [hh, hcard]
    unfold F
    push_cast
    ring
  rw [he] at hsum
  exact hend.trans hsum

theorem linear_loss {n k : ℕ} (hk : 1≤k) (hn : k*(k+1)≤n) :
    (n : ℝ)/(2*((k : ℝ)+1)^2)-1≤
      ∑ d∈Layer n k, ((n : ℝ)/d-k) := by
  have hkR : (1 : ℝ)≤k := by exact_mod_cast hk
  have hnR : (k : ℝ)*(k+1)≤n := by exact_mod_cast hn
  have hk0 : (0 : ℝ)<k := by linarith only [hkR]
  have hn0 : (0 : ℝ)<n := (mul_pos hk0 (by positivity : (0 : ℝ)<(k : ℝ)+1)).trans_le hnR
  have hlr := layer_nonempty hk hn
  have hl : 0<Left n k := Nat.zero_lt_succ _
  have hbounds := layer_bounds hk hn
  have hend := linear_endpoint hkR hnR hbounds.1 hbounds.2
  have hsum := Finset.sum_le_sum (s := Layer n k) (fun d hd =>
    linear_tangent (n := (n : ℝ)) (k := (k : ℝ)) (d := (d : ℝ)) hn0
      (by exact_mod_cast (hl.trans_le (Finset.mem_Icc.mp hd).1)))
  have hid := sum_Icc_cast hlr
  change (∑ d∈Layer n k, (d : ℝ))=((Layer n k).card : ℝ)*
    ((Left n k : ℝ)+Right n k)/2 at hid
  have he : (∑ d∈Layer n k, ((k : ℝ)-(k : ℝ)^2*d/n))=
      ((Layer n k).card : ℝ)*((k : ℝ)-(k : ℝ)^2*((Left n k : ℝ)+Right n k)/(2*n)) := by
    have hterm : ∀ d : ℕ, (k : ℝ)^2*d/n=((k : ℝ)^2/n)*(d : ℝ) := by intro d; ring
    simp_rw [hterm]
    rw [Finset.sum_sub_distrib, ←Finset.mul_sum]
    simp only [Finset.sum_const, nsmul_eq_mul]
    rw [hid]
    ring
  rw [he] at hsum
  exact hend.trans hsum

#print axioms nat_div_bounds
#print axioms layer_nonempty
#print axioms layer_quotient
#print axioms layer_bounds
#print axioms sum_consecutive
#print axioms sum_Icc_cast
#print axioms square_loss
#print axioms linear_loss
end
end JSP233.APLayerSum80470
