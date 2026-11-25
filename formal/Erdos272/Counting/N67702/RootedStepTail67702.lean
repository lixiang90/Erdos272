module

public import Erdos272.Capacity.LowSteps32
public import Erdos272.Arithmetic.N158375.MidpointSquare158375

@[expose] public section
namespace JSP233.StarMidpoint67702
open StarCompletion StarResources30 CrossLine30 JointResources31 HarmonicAbel29
open LowSteps32 APGeometry
open scoped Classical BigOperators
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1500000

theorem reciprocal_square_tail (m n : ℕ) :
    (∑ d ∈ Finset.Icc (m+1) n, (1 : ℝ)/(d : ℝ)^2) ≤ 2/(2*(m : ℝ)+1) := by
  by_cases hn : m ≤ n
  · have hs : (∑ d ∈ Finset.Icc (m+1) n, (1 : ℝ)/(d : ℝ)^2) ≤
        2/(2*(m : ℝ)+1)-2/(2*(n : ℝ)+1) := by
      induction n, hn using Nat.le_induction with
      | base =>
          rw [Finset.Icc_eq_empty_of_lt (by omega)]
          simp
      | succ n hn ih =>
          rw [Finset.sum_Icc_succ_top (by omega)]
          have hh := StarMidpoint158375.half_square_step n
          push_cast
          have he : (2 : ℝ)*((n : ℝ)+1)+1=2*(n : ℝ)+3 := by ring
          rw [he]
          linarith only [ih, hh]
    have hp : (0 : ℝ) ≤ 2/(2*(n : ℝ)+1) := by positivity
    linarith only [hs, hp]
  · have he : Finset.Icc (m+1) n = ∅ := Finset.Icc_eq_empty_of_lt (by omega)
    rw [he]
    positivity

theorem finite_class_total (m n : ℕ) (J : Finset ℕ) (a : ℕ→ℝ) (active : ℕ→Prop)
    (L R : ℝ) (hL : 0≤L) (hR : 0≤R) (hJ : J⊆Finset.Icc 1 n)
    (hcount : ∀ d∈J, a d≤(if active d then L*R/(d:ℝ)^2 else 0)+2*(n:ℝ)/(d:ℝ)+1) :
    (∑ d∈J, a d)≤(∑ d∈J.filter (fun d => active d ∧ d≤m), a d)
      +L*R*(2/(2*(m : ℝ)+1))+2*(n:ℝ)*Harmonic n+n := by
  let low := J.filter (fun d => active d ∧ d≤m)
  let rest := J\low
  let B := rest.filter active
  have hrJ : rest⊆Finset.Icc 1 n := (Finset.sdiff_subset).trans hJ
  have hB : B⊆Finset.Icc (m+1) n := by
    intro d hd
    obtain ⟨hdr,hact⟩ := Finset.mem_filter.mp hd
    obtain ⟨hdJ,hdlow⟩ := Finset.mem_sdiff.mp hdr
    obtain ⟨hd1,hdn⟩ := Finset.mem_Icc.mp (hJ hdJ)
    have hd5 : ¬d≤m := by
      intro hh
      exact hdlow (Finset.mem_filter.mpr ⟨hdJ,hact,hh⟩)
    exact Finset.mem_Icc.mpr ⟨by omega,hdn⟩
  have htail : (∑ d∈B, (1:ℝ)/(d:ℝ)^2)≤2/(2*(m : ℝ)+1) := by
    calc
      _≤∑ d∈Finset.Icc (m+1) n, (1:ℝ)/(d:ℝ)^2 :=
        Finset.sum_le_sum_of_subset_of_nonneg hB (by intro d hd hn; positivity)
      _≤2/(2*(m : ℝ)+1) := reciprocal_square_tail m n
  have hprod : (∑ d∈rest, if active d then L*R/(d:ℝ)^2 else 0)≤L*R*(2/(2*(m : ℝ)+1)) := by
    rw [←Finset.sum_filter]
    change (∑ d∈B, L*R/(d:ℝ)^2)≤L*R*(2/(2*(m : ℝ)+1))
    have he (d : ℕ) : L*R/(d:ℝ)^2=L*R*((1:ℝ)/(d:ℝ)^2) := by ring
    simp_rw [he]
    rw [←Finset.mul_sum]
    simpa only [one_div,div_eq_mul_inv,one_mul] using
      mul_le_mul_of_nonneg_left htail (mul_nonneg hL hR)
  have hhar : (∑ d∈rest, (1:ℝ)/(d:ℝ))≤Harmonic n := by
    exact Finset.sum_le_sum_of_subset_of_nonneg hrJ (by intro d hd hn; positivity)
  have hlin : (∑ d∈rest, 2*(n:ℝ)/(d:ℝ))≤2*(n:ℝ)*Harmonic n := by
    have he (d : ℕ) : 2*(n:ℝ)/(d:ℝ)=2*(n:ℝ)*((1:ℝ)/(d:ℝ)) := by ring
    simp_rw [he]
    rw [←Finset.mul_sum]
    exact mul_le_mul_of_nonneg_left hhar (by positivity)
  have hcard : (rest.card:ℝ)≤n := by
    have hh := Finset.card_le_card hrJ
    have hI : (Finset.Icc 1 n).card=n := by simp
    rw [hI] at hh
    exact_mod_cast hh
  have hrest := Finset.sum_le_sum (s:=rest) (fun d hd => hcount d (Finset.mem_sdiff.mp hd).1)
  simp only [Finset.sum_add_distrib,Finset.sum_const,nsmul_eq_mul,mul_one] at hrest
  have hpart := Finset.sum_sdiff (f:=a) (Finset.filter_subset (fun d => active d ∧ d≤m) J)
  change (∑ d∈rest,a d)+(∑ d∈low,a d)=∑ d∈J,a d at hpart
  change (∑ d∈J,a d)≤(∑ d∈low,a d)+L*R*(2/(2*(m : ℝ)+1))+2*(n:ℝ)*Harmonic n+n
  linarith

def LowActive (m : ℕ) (c : ℤ) (F : Finset (Finset ℤ)) : Finset ℕ :=
  (NatLabels c F).filter (fun d => (d : ℤ) ∈ APActiveSteps c F ∧ d≤m)

theorem actual_AP_total (m N : ℕ) (c : ℤ) (F : Finset (Finset ℤ))
    (hground : ∀ S∈F, S⊆Ground N) (hAP : ∀ S∈F, IsAP S)
    (hroot : Rooted F c) (hlarge : ∀ S∈F, 4≤S.card) (hc : c∈Ground N) :
    (F.card:ℝ)≤(∑ d∈LowActive m c F, ((StepClass F (trueStep c) (d:ℤ)).card:ℝ))
      +(((N-1:ℕ):ℝ)^2/(2*(2*(m : ℝ)+1)))+2*((N-1:ℕ):ℝ)*Harmonic (N-1)+((N-1:ℕ):ℝ) := by
  have hcI : 1≤c ∧ c≤(N:ℤ) := by
    rw [StarBoundConcrete30.ground_eq_Icc] at hc
    exact Finset.mem_Icc.mp hc
  have hl : (leftCapacity c:ℤ)=c-1 := Int.toNat_of_nonneg (by omega)
  have hr : (rightCapacity N c:ℤ)=(N:ℤ)-c := Int.toNat_of_nonneg (by omega)
  have hcap : leftCapacity c+rightCapacity N c=N-1 := by omega
  have hcapR : (leftCapacity c:ℝ)+(rightCapacity N c:ℝ)=((N-1:ℕ):ℝ) := by exact_mod_cast hcap
  have hJ := nat_labels_bound N c F hground hAP hroot hlarge
  have hh := finite_class_total m (N-1) (NatLabels c F)
    (fun d => ((StepClass F (trueStep c) (d:ℤ)).card:ℝ))
    (fun d => (d:ℤ)∈APActiveSteps c F) (leftCapacity c:ℝ) (rightCapacity N c:ℝ)
    (Nat.cast_nonneg _) (Nat.cast_nonneg _) hJ (by
      intro d hd
      have hdpos : 0<d := by have := (Finset.mem_Icc.mp (hJ hd)).1; omega
      have hb := actual_class_count N c F hground hAP hroot hlarge hc d hdpos
      rw [hcapR] at hb
      by_cases ha : (d:ℤ)∈APActiveSteps c F
      · simpa only [if_pos ha] using hb
      · simpa only [if_neg ha] using hb)
  rw [sum_nat_class_card c F hAP hroot] at hh
  have hp : (leftCapacity c:ℝ)*(rightCapacity N c:ℝ)≤((N-1:ℕ):ℝ)^2/4 := by
    nlinarith [sq_nonneg ((leftCapacity c:ℝ)-(rightCapacity N c:ℝ))]
  have hh' : (F.card:ℝ)≤(∑ d∈LowActive m c F, ((StepClass F (trueStep c) (d:ℤ)).card:ℝ))
      +(leftCapacity c:ℝ)*(rightCapacity N c:ℝ)*(2/(2*(m : ℝ)+1))
      +2*((N-1:ℕ):ℝ)*Harmonic (N-1)+((N-1:ℕ):ℝ) := by
    convert hh using 1
    congr 4
    ext d
    simp only [LowActive,Finset.mem_filter]
  have hpaid := mul_le_mul_of_nonneg_right hp
    (show (0 : ℝ)≤2/(2*(m : ℝ)+1) by positivity)
  have he : (((N-1 : ℕ) : ℝ)^2/4)*(2/(2*(m : ℝ)+1))=
      ((N-1 : ℕ) : ℝ)^2/(2*(2*(m : ℝ)+1)) := by
    field_simp
    <;> ring
  rw [he] at hpaid
  linarith only [hh',hpaid]

end
end JSP233.StarMidpoint67702
