module

public import Erdos272.Counting.N67702.RootedStepTail67702
public import Erdos272.Arithmetic.HarmonicSharp39

@[expose] public section
namespace JSP233.RootedArms20258
open StarCompletion StarResources30 CrossLine30 JointResources31 LowSteps32 APGeometry
open AffineLine30 StaircaseGeometry HarmonicAbel29
open scoped Classical BigOperators
noncomputable section
set_option autoImplicit false

/-- For an inactive step the short arm has at most two values. The linear
term is controlled by the longer arm, including when the root is off centre. -/
private theorem actual_class {N d : ℕ} {c : ℤ} {F : Finset (Finset ℤ)}
    (ground : ∀ S ∈ F, S ⊆ Ground N) (ap : ∀ S ∈ F, IsAP S)
    (root : Rooted F c) (large : ∀ S ∈ F, 4 ≤ S.card) (hc : c ∈ Ground N)
    (label : d ∈ NatLabels c F) :
    let L := leftCapacity c
    let R := rightCapacity N c
    d ∈ Finset.Icc 1 (max L R) ∧
      ((StepClass F (trueStep c) (d : ℤ)).card : ℝ) ≤
        (if (d : ℤ) ∈ APActiveSteps c F then (L : ℝ)*R/(d : ℝ)^2 else 0)
          +2*(max L R : ℕ)/(d : ℝ)+1 := by
  dsimp only
  let M := max (leftCapacity c) (rightCapacity N c)
  have hlM : leftCapacity c ≤ M := le_max_left _ _
  have hrM : rightCapacity N c ≤ M := le_max_right _ _
  obtain ⟨e,he,ed⟩ := Finset.mem_image.mp label
  have ep := actual_step_labels_positive c F ap root e he
  have eq : (d : ℤ) = e := by omega
  have hd : 0 < d := by omega
  have hdR : (0 : ℝ) < d := by exact_mod_cast hd
  obtain ⟨C,hC,valid,bounds⟩ := actual_class_coordinates N c F ground ap root large hc d hd
  have card : (StepClass F (trueStep c) (d : ℤ)).card=C.card := by
    rw [←hC,mapFamily_card c (d : ℤ) (by exact_mod_cast hd),family_card]
  obtain ⟨S,hS,hstep⟩ := Finset.mem_image.mp he
  have member : S ∈ StepClass F (trueStep c) (d : ℤ) :=
    Finset.mem_filter.mpr ⟨hS,hstep.trans eq.symm⟩
  have cp : 0 < C.card := card ▸ Finset.card_pos.mpr ⟨S,member⟩
  obtain ⟨p,hp⟩ := Finset.card_pos.mp cp
  obtain ⟨pl,pr⟩ := bounds p hp
  have plen := valid p hp
  constructor
  · apply Finset.mem_Icc.mpr
    refine ⟨hd,?_⟩
    by_cases pos : 1 ≤ p.1
    · exact (Nat.le_mul_of_pos_left d pos).trans (pl.trans hlM)
    · exact (Nat.le_mul_of_pos_left d (by omega : 0 < p.2)).trans (pr.trans hrM)
  · rw [card]
    have l : Height C ≤ leftCapacity c/d := Finset.sup_le
      (fun p hp => (Nat.le_div_iff_mul_le hd).mpr (bounds p hp).1)
    have r : Width C ≤ rightCapacity N c/d := Finset.sup_le
      (fun p hp => (Nat.le_div_iff_mul_le hd).mpr (bounds p hp).2)
    have h : (Height C : ℝ) ≤ (leftCapacity c : ℝ)/d :=
      (le_div_iff₀ hdR).mpr (by exact_mod_cast (Nat.le_div_iff_mul_le hd).mp l)
    have w : (Width C : ℝ) ≤ (rightCapacity N c : ℝ)/d :=
      (le_div_iff₀ hdR).mpr (by exact_mod_cast (Nat.le_div_iff_mul_le hd).mp r)
    have hm := h.trans (div_le_div_of_nonneg_right (by exact_mod_cast hlM : (leftCapacity c : ℝ) ≤ M) hdR.le)
    have wm := w.trans (div_le_div_of_nonneg_right (by exact_mod_cast hrM : (rightCapacity N c : ℝ) ≤ M) hdR.le)
    have box : (C.card : ℝ) ≤ (Height C : ℝ)*(Width C : ℝ)+Height C+Width C := by
      exact_mod_cast valid_coordinates_card C valid
    have linear : 2*(M : ℝ)/d=2*((M : ℝ)/d) := by ring
    by_cases active : (d : ℤ) ∈ APActiveSteps c F
    · rw [if_pos active]
      have area := mul_le_mul h w (Nat.cast_nonneg (Width C))
        (div_nonneg (Nat.cast_nonneg (leftCapacity c)) hdR.le)
      rw [div_mul_div_comm,←pow_two] at area
      change (C.card : ℝ) ≤ _+2*(M : ℝ)/d+1
      rw [linear]
      linarith only [box,area,hm,wm]
    · rw [if_neg active,zero_add]
      change (C.card : ℝ) ≤ 2*(M : ℝ)/d+1
      rw [linear]
      rcases coordinates_thin_of_inactive c d F C hC active with thin|thin
      · have ht : (Height C : ℝ) ≤ 1 := by exact_mod_cast thin
        nlinarith only [box,ht,wm,mul_le_mul_of_nonneg_right ht (Nat.cast_nonneg (Width C))]
      · have wt : (Width C : ℝ) ≤ 1 := by exact_mod_cast thin
        nlinarith only [box,wt,hm,mul_le_mul_of_nonneg_left wt (Nat.cast_nonneg (Height C))]

/-- The quadratic tail loses a square when the two arms have unequal lengths.
This square pays for the imbalance in the harmonic tail. -/
theorem actual_ten {N : ℕ} {c : ℤ} {F : Finset (Finset ℤ)} (hi : N < 2^16)
    (ground : ∀ S ∈ F, S ⊆ Ground N) (ap : ∀ S ∈ F, IsAP S)
    (root : Rooted F c) (large : ∀ S ∈ F, 4 ≤ S.card) (hc : c ∈ Ground N) :
    let n : ℝ := ((N-1 : ℕ) : ℝ)
    (F.card : ℝ) ≤ (∑ d ∈ StarMidpoint67702.LowActive 10 c F,
      ((StepClass F (trueStep c) (d : ℤ)).card : ℝ))+n^2/42+(25/2)*n+1641 := by
  let L := leftCapacity c
  let R := rightCapacity N c
  let M := max L R
  have hI := (mem_ground N c).mp hc
  have l : (L : ℤ) = c-1 := Int.toNat_of_nonneg (by omega)
  have r : (R : ℤ) = (N : ℤ)-c := Int.toNat_of_nonneg (by omega)
  have sum : L+R=N-1 := by omega
  have sc : (L : ℝ)+R=((N-1 : ℕ) : ℝ) := by exact_mod_cast sum
  have ml : M ≤ N-1 := by dsimp only [M]; omega
  have H : Harmonic M ≤ 12 :=
    (HarmonicSharp39.actual_harmonic_tight M 16 (by omega)).trans (by norm_num)
  have scaled := mul_le_mul_of_nonneg_left H (show 0 ≤ 2*(M : ℝ) by positivity)
  have classes := fun {d : ℕ} (hd : d ∈ NatLabels c F) => actual_class ground ap root large hc hd
  have hh := StarMidpoint67702.finite_class_total 10 M (NatLabels c F)
    (fun d => ((StepClass F (trueStep c) (d : ℤ)).card : ℝ))
    (fun d => (d : ℤ) ∈ APActiveSteps c F) (L : ℝ) (R : ℝ)
    (Nat.cast_nonneg _) (Nat.cast_nonneg _) (fun _ hd => (classes hd).1) (by
      intro d hd
      by_cases active : (d : ℤ) ∈ APActiveSteps c F <;>
        simpa only [L,R,M,active,ite_true,ite_false,eq_self,not_false_eq_true] using (classes hd).2)
  rw [sum_nat_class_card c F ap root] at hh
  norm_num only [Nat.cast_ofNat,show (2*(10 : ℝ)+1) = 21 by norm_num] at hh
  let low := ∑ d ∈ StarMidpoint67702.LowActive 10 c F, ((StepClass F (trueStep c) (d : ℤ)).card : ℝ)
  have paid : (F.card : ℝ) ≤ low+(L : ℝ)*R*(2/21)+2*(M : ℝ)*Harmonic M+M := by
    apply hh.trans
    apply add_le_add ?_ (le_refl _)
    apply add_le_add ?_ (le_refl _)
    apply add_le_add ?_ (le_refl _)
    dsimp only [low,StarMidpoint67702.LowActive]
    apply Finset.sum_le_sum_of_subset_of_nonneg
    · intro d hd
      simpa only [Finset.mem_filter] using hd
    · intro d _ _
      positivity
  change (F.card : ℝ) ≤ low+_/42+_*_+1641
  rw [←sc]
  rcases le_total L R with h|h
  · have e : M=R := max_eq_right h
    rw [e] at paid scaled
    nlinarith only [paid,scaled,sq_nonneg (2*((R : ℝ)-L)-525)]
  · have e : M=L := max_eq_left h
    rw [e] at paid scaled
    nlinarith only [paid,scaled,sq_nonneg (2*((L : ℝ)-R)-525)]

#print axioms actual_ten
end
end JSP233.RootedArms20258
