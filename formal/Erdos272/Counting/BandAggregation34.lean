module

public import Erdos272.Resources.StarBoundConcrete30
public import Mathlib.Data.Nat.Log
public import Mathlib.Algebra.Order.BigOperators.Group.Finset
public import Mathlib.Algebra.BigOperators.Ring.Finset

@[expose] public section

/-! Actual rank-band aggregation and the two-scale trace arithmetic.
The KK band estimate remains an explicit input, not an axiom. -/
namespace JSP233.BandAggregation34
open StarCompletion
open scoped Classical BigOperators
noncomputable section

theorem split_trace_payment (J D₁ D₂ K i C H : ℕ)
    (hJ : 1≤J) (hD₂ : 1≤D₂) (hi : i≤D₁)
    (hsize : 8*J*D₁*D₂+D₁≤K) (hH : K≤H) (hC : H≤C+i) :
    8*J*i*D₂≤C ∧ K≤2*C ∧ 8*J*D₁≤K := by
  have hm := Nat.mul_le_mul_left (8*J*D₂) hi
  have hd := Nat.mul_le_mul_left (8*J*D₁) hD₂
  have hj := Nat.mul_le_mul_right D₁ hJ
  constructor
  · nlinarith
  constructor <;> nlinarith

theorem dyadic_sum (n : ℕ) :
    (∑ j∈Finset.range n, (1/2:ℝ)^j)=2*(1-(1/2:ℝ)^n) := by
  induction n with
  | zero => simp
  | succ n ih => rw [Finset.sum_range_succ,ih,pow_succ]; ring

theorem dyadic_sum_le_two (n : ℕ) :
    (∑ j∈Finset.range n, (1/2:ℝ)^j)≤2 := by
  rw [dyadic_sum]
  have hp : 0≤(1/2:ℝ)^n := pow_nonneg (by norm_num) _
  linarith

theorem weighted_band_sum (n K A : ℕ) (m : ℕ→ℕ) (hK : 0<K)
    (hcap : ∀ j<n, m j*(2^j*K)≤A) :
    (∑ j∈Finset.range n, m j)*K≤2*A := by
  have hrow : ∀ j∈Finset.range n, (m j:ℝ)*K≤(A:ℝ)*(1/2:ℝ)^j := by
    intro j hj
    have hc : (m j:ℝ)*((2:ℝ)^j*K)≤A := by
      exact_mod_cast hcap j (Finset.mem_range.mp hj)
    have hp : 0<(2:ℝ)^j := pow_pos (by norm_num) _
    have hh := (div_le_div_of_nonneg_right hc hp.le)
    have he : ((m j:ℝ)*((2:ℝ)^j*K))/((2:ℝ)^j)=(m j:ℝ)*K := by
      field_simp
    rw [he] at hh
    simpa only [one_div_pow,div_eq_mul_inv,one_mul,inv_pow] using hh
  have hs := Finset.sum_le_sum hrow
  rw [←Finset.sum_mul,←Finset.mul_sum] at hs
  have ht := mul_le_mul_of_nonneg_left (dyadic_sum_le_two n) (by positivity : (0:ℝ)≤A)
  have hh : ((∑ j∈Finset.range n, m j):ℝ)*K≤2*A := by
    exact hs.trans (by nlinarith)
  exact_mod_cast hh

def RankBand {α : Type*} [DecidableEq α] (F : Finset α) (rank : α→ℕ) (K j : ℕ) : Finset α :=
  F.filter (fun S => 16*(2^j*K)+1≤rank S ∧ rank S≤32*(2^j*K))

theorem actual_rank_band_cover {α : Type*} [DecidableEq α] (F : Finset α) (rank : α→ℕ)
    (N K : ℕ) (hK : 0<K) (hlow : ∀ S∈F, 16*K+1≤rank S)
    (hhigh : ∀ S∈F, rank S≤N) :
    F⊆(Finset.range (N+1)).biUnion (RankBand F rank K) := by
  intro S hS
  let q := (rank S-1)/(16*K)
  have hq : 0<q := by
    apply Nat.div_pos
    · have hh := hlow S hS; omega
    · positivity
  let j := Nat.log 2 q
  have hl := Nat.pow_log_le_self 2 (by omega : q≠0)
  have hu := Nat.lt_pow_succ_log_self (by decide : 1<2) q
  have hprod := Nat.div_mul_le_self (rank S-1) (16*K)
  have hquot : rank S-1 < (2^(j+1))*(16*K) := by
    apply (Nat.div_lt_iff_lt_mul (by positivity : 0<16*K)).mp
    exact hu
  have hqN : q≤N := (Nat.div_le_self _ _).trans (by have hh := hhigh S hS; omega)
  have hjN : j≤N := (Nat.log_le_self 2 q).trans hqN
  change 2^j≤q at hl
  have hpos : 1≤rank S := by have h := hlow S hS; omega
  have he : rank S-1+1=rank S := by omega
  refine Finset.mem_biUnion.mpr ⟨j,Finset.mem_range.mpr (by omega),?_⟩
  apply Finset.mem_filter.mpr
  refine ⟨hS,?_,?_⟩
  · have hh := Nat.mul_le_mul_right (16*K) hl
    change q*(16*K)≤rank S-1 at hprod
    nlinarith
  · rw [pow_succ] at hquot
    nlinarith

theorem actual_large_from_band_budget (N K J : ℕ) (F : Finset (Finset ℤ))
    (hK : 0<K) (hground : ∀ S∈F, S⊆Ground N)
    (hlow : ∀ S∈F, 16*K+1≤S.card)
    (hband : ∀ j<N+1,
      (RankBand F Finset.card K j).card*(2^j*(15*K))≤
        261*N^2+1920*J*N.choose 2) :
    15*K*F.card≤522*N^2+3840*J*N.choose 2 := by
  have hhigh : ∀ S∈F, S.card≤N := by
    intro S hS
    simpa only [ground_card] using Finset.card_le_card (hground S hS)
  have hc := actual_rank_band_cover F Finset.card N K hK hlow hhigh
  have hcard := (Finset.card_le_card hc).trans Finset.card_biUnion_le
  have hw := weighted_band_sum (N+1) (15*K) (261*N^2+1920*J*N.choose 2)
    (fun j => (RankBand F Finset.card K j).card) (by positivity) hband
  have hm := Nat.mul_le_mul_right (15*K) hcard
  nlinarith

#print axioms split_trace_payment
#print axioms dyadic_sum
#print axioms dyadic_sum_le_two
#print axioms weighted_band_sum
#print axioms actual_rank_band_cover
#print axioms actual_large_from_band_budget
end
end JSP233.BandAggregation34
