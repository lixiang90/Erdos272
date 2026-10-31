import Erdos272.Arithmetic.WindowCounts208

namespace JSP233.CleanupNet208
open scoped BigOperators
set_option maxHeartbeats 0

def Ceil (a b : ℕ) : ℕ := (a+b-1)/b

theorem le_ceil_mul {a b : ℕ} (hb : 0<b) : a ≤ Ceil a b*b := by
  have hh := (WindowCounts208.rightLeft_le (q:=a) (J:=0) (B:=b)
    (r:=WindowCounts208.RightLeft a 0 b) hb).mp le_rfl
  simpa only [WindowCounts208.RightLeft,Nat.sub_zero,Nat.zero_add,Ceil] using hh

section
variable {ι : Type*} [DecidableEq ι] (s : Finset ι) (T E z H : ι → ℕ)
variable {G low high i : ℕ}

theorem band_grid_bound (hG : 0<G) (hlo : 0<low) (hlh : low ≤ high)
    (hET : ∀ b ∈ s,E b ≤ T b) (hEi : ∀ b ∈ s,E b ≤ i)
    (hown : ∀ b ∈ s,0<H b → (T b-E b+1)*G ≤ min G (z b)*high)
    {b : ι} (hb : b ∈ s) (hH : 0<H b) :
    T b*G ≤ (min G (∑ a ∈ s,z a)+Ceil (i*G) low)*high := by
  have hz : z b ≤ ∑ a ∈ s,z a := Finset.single_le_sum (fun a ha=>Nat.zero_le (z a)) hb
  have hm := Nat.mul_le_mul_right high (min_le_min_left G hz)
  have ho := (hown b hb hH).trans hm
  have he := (le_ceil_mul (a:=i*G) hlo).trans (Nat.mul_le_mul_left (Ceil (i*G) low) hlh)
  have ht : T b ≤ T b-E b+1+i := by have :=hET b hb;have :=hEi b hb;omega
  have hmul := Nat.mul_le_mul_right G ht
  rw [Nat.add_mul] at hmul
  rw [Nat.add_mul]
  omega

theorem band_coefficient_nonneg (hG : 0<G) (hlo : 0<low) (hlh : low ≤ high)
    (hET : ∀ b ∈ s,E b ≤ T b) (hEi : ∀ b ∈ s,E b ≤ i)
    (hown : ∀ b ∈ s,0<H b → (T b-E b+1)*G ≤ min G (z b)*high)
    {b : ι} (hb : b ∈ s) (hH : 0<H b) :
    0 ≤ ((min G (∑ a ∈ s,z a)+Ceil (i*G) low : ℕ) : ℝ)/G-(T b : ℝ)/high := by
  have hh := band_grid_bound s T E z H hG hlo hlh hET hEi hown hb hH
  have hhigh : (0 : ℝ)<high := by exact_mod_cast (by omega : 0<high)
  have hgrid : (0 : ℝ)<G := by exact_mod_cast hG
  apply sub_nonneg.mpr
  rw [div_le_div_iff₀ hhigh hgrid]
  exact_mod_cast hh

theorem floor_credit_le (hhigh : 0<high) (hG : 0<G) (t : ℕ) :
    ((t*G/high : ℕ) : ℝ)/G ≤ (t : ℝ)/high := by
  have hh := Nat.div_mul_le_self (t*G) high
  have hhr : (0 : ℝ)<high := by exact_mod_cast hhigh
  have hgr : (0 : ℝ)<G := by exact_mod_cast hG
  rw [div_le_div_iff₀ hgr hhr]
  exact_mod_cast hh

theorem credit_le_net_base (hG : 0<G) (hlo : 0<low) (hlh : low ≤ high)
    (hET : ∀ b ∈ s,E b ≤ T b) (hEi : ∀ b ∈ s,E b ≤ i)
    (hown : ∀ b ∈ s,0<H b → (T b-E b+1)*G ≤ min G (z b)*high) :
    (∑ b ∈ s,H b*(T b*G/high)) ≤ (∑ b ∈ s,H b)*(min G (∑ b ∈ s,z b)+Ceil (i*G) low) := by
  have hp : ∀ b ∈ s,H b*(T b*G/high) ≤ H b*(min G (∑ a ∈ s,z a)+Ceil (i*G) low) := by
    intro b hb
    by_cases hz : H b=0
    · simp only [hz,Nat.zero_mul,le_refl]
    · have hh := band_grid_bound s T E z H hG hlo hlh hET hEi hown hb (by omega)
      have hd := Nat.div_le_div_right (c:=high) hh
      have hp : 0<high := by omega
      rw [Nat.mul_div_cancel _ hp] at hd
      exact Nat.mul_le_mul_left (H b) hd
  have hs := Finset.sum_le_sum hp
  rw [←Finset.sum_mul] at hs
  exact hs

theorem actual_count_substitution (hG : 0<G) (hlo : 0<low) (hlh : low ≤ high)
    (hET : ∀ b ∈ s,E b ≤ T b) (hEi : ∀ b ∈ s,E b ≤ i)
    (hown : ∀ b ∈ s,0<H b → (T b-E b+1)*G ≤ min G (z b)*high)
    (actual : ι → ℕ) (ha : ∀ b ∈ s,actual b ≤ H b) :
    (∑ b ∈ s,(actual b : ℝ)*
        (((min G (∑ a ∈ s,z a)+Ceil (i*G) low : ℕ) : ℝ)/G-(T b : ℝ)/high)) ≤ 
      (((∑ b ∈ s,H b)*(min G (∑ a ∈ s,z a)+Ceil (i*G) low)-
        (∑ b ∈ s,H b*(T b*G/high)) : ℕ) : ℝ)/G := by
  let Z:=min G (∑ a ∈ s,z a)+Ceil (i*G) low
  let C:=∑ b ∈ s,H b*(T b*G/high)
  let total:=∑ b ∈ s,H b
  have hcoef : ∀ b ∈ s,0<H b → 0 ≤ (Z : ℝ)/G-(T b : ℝ)/high := by
    intro b hb hh
    exact band_coefficient_nonneg s T E z H hG hlo hlh hET hEi hown hb hh
  have hsub : (∑ b ∈ s,(actual b : ℝ)*((Z : ℝ)/G-(T b : ℝ)/high)) ≤ 
      ∑ b ∈ s,(H b : ℝ)*((Z : ℝ)/G-(T b : ℝ)/high) := by
    apply Finset.sum_le_sum
    intro b hb
    by_cases hz : H b=0
    · have haz : actual b=0 := by have :=ha b hb;omega
      simp only [hz,haz,Nat.cast_zero,zero_mul,le_refl]
    · exact mul_le_mul_of_nonneg_right (by exact_mod_cast ha b hb) (hcoef b hb (by omega))
  have hc : (C : ℝ)/G ≤ ∑ b ∈ s,(H b : ℝ)*((T b : ℝ)/high) := by
    change ((∑ b ∈ s,H b*(T b*G/high) : ℕ) : ℝ)/G ≤ _
    rw [Nat.cast_sum,Finset.sum_div]
    apply Finset.sum_le_sum
    intro b hb
    rw [Nat.cast_mul,mul_div_assoc]
    exact mul_le_mul_of_nonneg_left (floor_credit_le (by omega : 0<high) hG (T b)) (by positivity)
  have hn : C ≤ total*Z := credit_le_net_base s T E z H hG hlo hlh hET hEi hown
  have hr : (((total*Z-C : ℕ) : ℝ)/G)=(total : ℝ)*(Z : ℝ)/G-(C : ℝ)/G := by
    rw [Nat.cast_sub hn,Nat.cast_mul,sub_div]
  change _ ≤ ((total*Z-C : ℕ) : ℝ)/G
  rw [hr]
  have hs : (∑ b ∈ s,(H b : ℝ)*((Z : ℝ)/G-(T b : ℝ)/high))=
      (total : ℝ)*(Z : ℝ)/G-(∑ b ∈ s,(H b : ℝ)*((T b : ℝ)/high)) := by
    simp_rw [mul_sub]
    rw [Finset.sum_sub_distrib,←Finset.sum_mul]
    simp only [total,Nat.cast_sum,mul_div_assoc]
  rw [hs] at hsub
  linarith
end

#print axioms band_coefficient_nonneg
#print axioms actual_count_substitution
end JSP233.CleanupNet208
