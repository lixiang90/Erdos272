module

public import Mathlib.Data.Nat.Choose.Cast
public import Erdos272.Core.N130000.StarCore130000

@[expose] public section

namespace JSP233.ThreeFiveArithmetic82427
open CoreUnionSource200000 StarArithmetic158375 StarArithmetic130000
open scoped Classical BigOperators
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1500000

def ChordBonus (a : ℕ) : ℕ := (a/15).choose 2-(a/30+1).choose 2

def HalfBonus (n : ℕ) : ℕ := n.choose 2-(n/2+1).choose 2

def PairLoss (b q : ℕ) : ℕ := ((b+2*q-1)/(2*q)).choose 2

theorem pair_loss_three (b : ℕ) : PairLoss b 3=((b+5)/6).choose 2 := by
  unfold PairLoss
  rw [show b+2*3-1=b+5 by omega]

theorem pair_loss_five (b : ℕ) : PairLoss b 5=((b+9)/10).choose 2 := by
  unfold PairLoss
  rw [show b+2*5-1=b+9 by omega]

theorem half_bonus_add_den (n : ℕ) :
    HalfBonus n+(n/2+1).choose 2=n.choose 2 := by
  by_cases hz : n=0
  · simp [HalfBonus, hz]
  · exact Nat.sub_add_cancel (Nat.choose_le_choose 2 (by omega : n/2+1≤n))

theorem chord_bonus_eq_half (a : ℕ) : ChordBonus a=HalfBonus (a/15) := by
  simp only [ChordBonus, HalfBonus, Nat.div_div_eq_div_mul]

theorem chord_bonus_add_den (a : ℕ) :
    ChordBonus a+(a/30+1).choose 2=(a/15).choose 2 := by
  simpa only [chord_bonus_eq_half, Nat.div_div_eq_div_mul, Nat.reduceMul] using
    half_bonus_add_den (a/15)

theorem chord_bonus_le_numerator (a : ℕ) : ChordBonus a≤(a/15).choose 2 :=
  Nat.sub_le _ _

theorem chord_bonus_zero {a : ℕ} (ha : a<45) : ChordBonus a=0 := by
  by_cases hsmall : a<30
  · have hc : (a/15).choose 2=0 := Nat.choose_eq_zero_of_lt (by omega)
    simp only [ChordBonus, hc, Nat.zero_sub]
  · have h₁ : a/15=2 := by omega
    have h₂ : a/30=1 := by omega
    norm_num [ChordBonus, h₁, h₂]

theorem half_bonus_step (n : ℕ) : HalfBonus n≤HalfBonus (n+1) := by
  have h₀ := half_bonus_add_den n
  have h₁ := half_bonus_add_den (n+1)
  have hc := choose_succ_two n
  by_cases he : (n+1)/2=n/2
  · rw [he] at h₁
    omega
  · have he' : (n+1)/2=n/2+1 := by omega
    have hd := choose_succ_two (n/2+1)
    rw [he'] at h₁
    have hn : n/2+1≤n := by omega
    omega

theorem half_bonus_mono {a b : ℕ} (hab : a≤b) : HalfBonus a≤HalfBonus b := by
  induction b, hab using Nat.le_induction with
  | base => exact le_rfl
  | succ b hab ih => exact ih.trans (half_bonus_step b)

theorem chord_bonus_mono {a b : ℕ} (hab : a≤b) : ChordBonus a≤ChordBonus b := by
  rw [chord_bonus_eq_half, chord_bonus_eq_half]
  exact half_bonus_mono (Nat.div_le_div_right hab)

theorem choose_split {u v n : ℕ} (huv : u+v≤n) :
    u.choose 2+v.choose 2≤n.choose 2 := by
  have hmono := Nat.choose_le_choose 2 huv
  have h₁ := APInterval208.choose_two_twice u
  have h₂ := APInterval208.choose_two_twice v
  have h₃ := APInterval208.choose_two_twice (u+v)
  nlinarith only [hmono, h₁, h₂, h₃, Nat.zero_le (u*v)]

theorem choose_shared_split {u v n : ℕ} (hu : 1≤u) (hv : 1≤v) (huv : u+v≤n+1) :
    u.choose 2+v.choose 2≤n.choose 2 := by
  have huR : (1 : ℝ)≤u := by exact_mod_cast hu
  have hvR : (1 : ℝ)≤v := by exact_mod_cast hv
  have hn : 1≤n := by omega
  have hnR : (1 : ℝ)≤n := by exact_mod_cast hn
  have hs : (u : ℝ)+v≤(n : ℝ)+1 := by exact_mod_cast huv
  have hp := mul_nonneg (sub_nonneg.mpr huR) (sub_nonneg.mpr hvR)
  have hgap := mul_nonneg (show 0≤(n : ℝ)-u-v+1 by linarith only [hs])
    (show 0≤(n : ℝ)+u+v-2 by linarith only [huR, hvR, hnR])
  have h₁ : 2*(u.choose 2 : ℝ)+(u : ℝ)=(u : ℝ)*(u : ℝ) := by
    exact_mod_cast APInterval208.choose_two_twice u
  have h₂ : 2*(v.choose 2 : ℝ)+(v : ℝ)=(v : ℝ)*(v : ℝ) := by
    exact_mod_cast APInterval208.choose_two_twice v
  have h₃ : 2*(n.choose 2 : ℝ)+(n : ℝ)=(n : ℝ)*(n : ℝ) := by
    exact_mod_cast APInterval208.choose_two_twice n
  have hh : (u.choose 2 : ℝ)+(v.choose 2 : ℝ)≤(n.choose 2 : ℝ) := by
    nlinarith only [h₁, h₂, h₃, hp, hgap]
  exact_mod_cast hh

theorem double_loss (b : ℕ) :
    ((b+5)/6).choose 2+((b+14)/15).choose 2≤(b/3).choose 2 := by
  by_cases hb : b<3
  · have h₁ : (b+5)/6≤1 := by omega
    have h₂ : (b+14)/15≤1 := by omega
    have hz₁ := Nat.choose_eq_zero_of_lt (show (b+5)/6<2 by omega)
    have hz₂ := Nat.choose_eq_zero_of_lt (show (b+14)/15<2 by omega)
    simp only [hz₁, hz₂, zero_add, Nat.zero_le]
  · exact choose_shared_split (by omega) (by omega) (by omega)

theorem sum_reserve {α : Type*} [DecidableEq α] {I : Finset α}
    (f g : α → ℕ) {p : α} {debt refund : ℕ}
    (hbase : ∀ q∈I, f q≤g q) (hp : p∈I) (hpay : f p+debt≤g p+refund) :
    (∑ q∈I, f q)+debt≤(∑ q∈I, g q)+refund := by
  have hrest : (∑ q∈I.erase p, f q)≤∑ q∈I.erase p, g q :=
    Finset.sum_le_sum (fun q hq => hbase q (Finset.mem_erase.mp hq).2)
  have hs₁ := Finset.sum_erase_add I f hp
  have hs₂ := Finset.sum_erase_add I g hp
  omega

theorem sum_losses {A : Finset ℕ} {b : ℕ} (hpos : ∀ q∈A, 0<q) :
    (∑ q∈A, PairLoss b q)≤∑ q∈A, (b/q).choose 2 := by
  exact Finset.sum_le_sum (fun q hq => half_loss b q (hpos q hq))

theorem sum_losses_except {A : Finset ℕ} {b p : ℕ}
    (hpos : ∀ q∈A, 0<q) (hp : p∈A) :
    (∑ q∈A, PairLoss b q)≤PairLoss b p+∑ q∈A.erase p, (b/q).choose 2 := by
  have hr := sum_losses (A := A.erase p) (b := b)
    (fun q hq => hpos q (Finset.mem_erase.mp hq).2)
  have hs := Finset.sum_erase_add A (PairLoss b) hp
  omega

theorem sum_double_losses {A : Finset ℕ} {b : ℕ}
    (hpos : ∀ q∈A, 0<q) (h₃ : 3∈A) :
    (∑ q∈A, PairLoss b q)+((b+14)/15).choose 2≤∑ q∈A, (b/q).choose 2 := by
  have hr := sum_losses_except (b := b) hpos h₃
  have hs := Finset.sum_erase_add A (fun q => (b/q).choose 2) h₃
  have hd := double_loss b
  change ((b+5)/6).choose 2+((b+14)/15).choose 2≤(b/3).choose 2 at hd
  rw [pair_loss_three] at hr
  omega

theorem inactive_plain_payment {a b p : ℕ} (hp : 0<p) (hbc : b≤(a+p-1)/p) :
    b.choose 2+(a/(2*p)).choose 2≤Weight a p+(b/2).choose 2 := by
  have hcon := divided_choose_contract (k := 2) (by decide) hbc
  have hdiv := StarCore130000.divided_ceil_lower a p 2 hp
  have hbonus : (a/(2*p)).choose 2≤(((a+p-1)/p)/2).choose 2 := by
    simpa only [Nat.mul_comm] using Nat.choose_le_choose 2 hdiv
  change b.choose 2+(a/(2*p)).choose 2≤((a+p-1)/p).choose 2+(b/2).choose 2
  omega

theorem three_inactive_payment {a b : ℕ} (hbc : b≤(a+2)/3) :
    b.choose 2+(a/6).choose 2+ChordBonus a+((b+9)/10).choose 2≤
      Weight a 3+(b/2).choose 2+(b/5).choose 2 := by
  let c := (a+2)/3
  have hpos : ∀ q∈({2,5} : Finset ℕ), 0<q := by
    intro q hq
    simp only [Finset.mem_insert, Finset.mem_singleton] at hq
    rcases hq with rfl | rfl <;> decide
  have hcon := divided_choose_sum_contract hpos
    (by norm_num : (∑ q∈({2,5} : Finset ℕ), (1 : ℝ)/(q : ℝ))≤1) hbc
  have hcon' : b.choose 2+(c/2).choose 2+(c/5).choose 2≤
      c.choose 2+(b/2).choose 2+(b/5).choose 2 := by
    simpa [c, add_assoc] using hcon
  have hh := Nat.choose_le_choose 2 (show a/6≤c/2 by dsimp only [c]; omega)
  have hn := Nat.choose_le_choose 2 (show a/15≤c/5 by dsimp only [c]; omega)
  have hl := Nat.choose_le_choose 2 (show (b+9)/10≤a/30+1 by omega)
  have hg := chord_bonus_add_den a
  change b.choose 2+(a/6).choose 2+ChordBonus a+((b+9)/10).choose 2≤
    c.choose 2+(b/2).choose 2+(b/5).choose 2
  omega

theorem five_inactive_payment {a b : ℕ} (hbc : b≤(a+4)/5) :
    b.choose 2+(a/10).choose 2+ChordBonus a+((b+5)/6).choose 2≤
      Weight a 5+(b/2).choose 2+(b/3).choose 2 := by
  let c := (a+4)/5
  have hpos : ∀ q∈({2,3} : Finset ℕ), 0<q := by
    intro q hq
    simp only [Finset.mem_insert, Finset.mem_singleton] at hq
    rcases hq with rfl | rfl <;> decide
  have hcon := divided_choose_sum_contract hpos
    (by norm_num : (∑ q∈({2,3} : Finset ℕ), (1 : ℝ)/(q : ℝ))≤1) hbc
  have hcon' : b.choose 2+(c/2).choose 2+(c/3).choose 2≤
      c.choose 2+(b/2).choose 2+(b/3).choose 2 := by
    simpa [c, add_assoc] using hcon
  have hh := Nat.choose_le_choose 2 (show a/10≤c/2 by dsimp only [c]; omega)
  have hn := Nat.choose_le_choose 2 (show a/15≤c/3 by dsimp only [c]; omega)
  have hl := Nat.choose_le_choose 2 (show (b+5)/6≤a/30+1 by omega)
  have hg := chord_bonus_add_den a
  change b.choose 2+(a/10).choose 2+ChordBonus a+((b+5)/6).choose 2≤
    c.choose 2+(b/2).choose 2+(b/3).choose 2
  omega

theorem inactive_five_extra (a : ℕ) :
    (a/10).choose 2+ChordBonus a≤Weight a 5 := by
  have hs := choose_split (show a/10+a/15≤(a+4)/5 by omega)
  have hg := chord_bonus_le_numerator a
  change (a/10).choose 2+ChordBonus a≤((a+4)/5).choose 2
  omega

theorem even_inactive_extra (a p : ℕ) (hp : p=3∨p=5) :
    (((a+1)/2)/p).choose 2+ChordBonus a≤Weight a p := by
  let n := (a+p-1)/p
  have hu : ((a+1)/2)/p≤(n+1)/2 := by
    rcases hp with rfl | rfl <;> dsimp only [n] <;> omega
  have hv : a/15≤n/3 := by
    rcases hp with rfl | rfl <;> dsimp only [n] <;> omega
  have hs := choose_split (show (n+1)/2+n/3≤n by omega)
  have h₁ := Nat.choose_le_choose 2 hu
  have h₂ := Nat.choose_le_choose 2 hv
  have hg := chord_bonus_le_numerator a
  change (((a+1)/2)/p).choose 2+ChordBonus a≤n.choose 2
  omega

theorem chord_bonus_quadratic (a : ℕ) :
    (a : ℝ)^2/600-(a : ℝ)/10≤(ChordBonus a : ℝ) := by
  let k := a/30
  let r := a%30
  have hr : r<30 := Nat.mod_lt a (by decide)
  have ha : a=30*k+r := by
    have hh := Nat.mod_add_div a 30
    dsimp only [k, r]
    omega
  have haR : (a : ℝ)=30*(k : ℝ)+(r : ℝ) := by exact_mod_cast ha
  have hden : a/30+1=k+1 := rfl
  have hb : (ChordBonus a : ℝ)+((a/30+1).choose 2 : ℝ)=((a/15).choose 2 : ℝ) := by
    exact_mod_cast chord_bonus_add_den a
  rw [hden] at hb
  have hkR := Nat.cast_nonneg (α := ℝ) k
  have hrR := Nat.cast_nonneg (α := ℝ) r
  by_cases hsmall : r<15
  · have hnum : a/15=2*k := by omega
    rw [hnum, Nat.cast_choose_two, Nat.cast_choose_two] at hb
    push_cast at hb
    have hrR' : (r : ℝ)<15 := by exact_mod_cast hsmall
    have h₁ := mul_nonneg hkR (show 0≤15-(r : ℝ) by linarith only [hrR'])
    have h₂ := mul_nonneg hrR (show 0≤60-(r : ℝ) by linarith only [hrR'])
    rw [haR]
    nlinarith only [hb, h₁, h₂]
  · have hnum : a/15=2*k+1 := by omega
    rw [hnum, Nat.cast_choose_two, Nat.cast_choose_two] at hb
    push_cast at hb
    have hrR' : (r : ℝ)<30 := by exact_mod_cast hr
    have h₁ := mul_nonneg hkR (show 0≤35-(r : ℝ) by linarith only [hrR'])
    have h₂ := mul_nonneg hrR (show 0≤60-(r : ℝ) by linarith only [hrR'])
    rw [haR]
    nlinarith only [hb, h₁, h₂]

#print axioms pair_loss_three
#print axioms pair_loss_five
#print axioms half_bonus_add_den
#print axioms chord_bonus_eq_half
#print axioms chord_bonus_add_den
#print axioms chord_bonus_le_numerator
#print axioms chord_bonus_zero
#print axioms half_bonus_step
#print axioms half_bonus_mono
#print axioms chord_bonus_mono
#print axioms choose_split
#print axioms choose_shared_split
#print axioms double_loss
#print axioms sum_reserve
#print axioms sum_losses
#print axioms sum_losses_except
#print axioms sum_double_losses
#print axioms inactive_plain_payment
#print axioms three_inactive_payment
#print axioms five_inactive_payment
#print axioms inactive_five_extra
#print axioms even_inactive_extra
#print axioms chord_bonus_quadratic
end
end JSP233.ThreeFiveArithmetic82427
