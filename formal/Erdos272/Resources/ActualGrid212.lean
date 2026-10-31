import Erdos272.Counting.OffResidue44
import Mathlib.Combinatorics.Enumerative.DoubleCounting

/-! The actual interval traces can be packed using their physical length
and the proved fringe width directly.  No cubic interval-size wrapper is
used, and no injectivity of the trace map is required. -/
namespace JSP233.ActualGrid212
open StarCompletion APGeometry OffResidue44
open scoped Classical BigOperators
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 0

theorem central_gate_real {n w k u p : ℝ}
    (hp : 1 < p) (hwidth : w < n / u)
    (hgate : (p - 1) * (p - 2) / 2 < n * (p / k - 1 - (p - 1) / u)) :
    n + 1 - w + p * (p - 1) / 2 < p * (n / k - w + 1) := by
  have hm := mul_lt_mul_of_pos_left hwidth (sub_pos.mpr hp)
  have hid : p * (n / k - w + 1) - (n + 1 - w + p * (p - 1) / 2) =
      (n * (p / k - 1 - (p - 1) / u) - (p - 1) * (p - 2) / 2) +
        ((p - 1) * (n / u) - (p - 1) * w) := by ring
  apply sub_pos.mp
  rw [hid]
  exact add_pos (sub_pos.mpr hgate) (sub_pos.mpr hm)

theorem actual_interval_ground_card {N L R : ℕ}
    (hL : 1 ≤ L) (hLR : L ≤ R) (hRN : R ≤ N) :
    ((Finset.Icc (L : ℤ) (R : ℤ)).card : ℝ) =
        (N : ℝ) + 1 - ((L : ℝ) + (N - R)) ∧
      ((Ground N \ Finset.Icc (L : ℤ) (R : ℤ)).card : ℝ) =
        (L : ℝ) + (N - R) - 1 := by
  have hsub : Finset.Icc (L : ℤ) (R : ℤ) ⊆ Ground N := by
    intro x hx
    have hh := Finset.mem_Icc.mp hx
    apply (mem_ground N x).mpr
    constructor <;> omega
  have hI : (Finset.Icc (L : ℤ) (R : ℤ)).card = R - L + 1 := by
    simp only [Int.card_Icc]
    omega
  have hIR : ((Finset.Icc (L : ℤ) (R : ℤ)).card : ℝ) =
      (N : ℝ) + 1 - ((L : ℝ) + (N - R)) := by
    rw [hI, Nat.cast_add, Nat.cast_sub hLR, Nat.cast_one]
    ring
  have he := Finset.card_sdiff_add_card_eq_card hsub
  rw [ground_card] at he
  have heR : ((Ground N \ Finset.Icc (L : ℤ) (R : ℤ)).card : ℝ) +
      (Finset.Icc (L : ℤ) (R : ℤ)).card = N := by exact_mod_cast he
  exact ⟨hIR, by linarith only [heR, hIR]⟩

/-- The rational continuous gate is applied to the cardinalities of the
actual central interval and its actual complement. -/
theorem actual_central_gate {N L R p : ℕ} {k u : ℝ}
    (hL : 1 ≤ L) (hLR : L ≤ R) (hRN : R ≤ N) (hp : 2 ≤ p)
    (hwidth : (L : ℝ) + (N - R) < (N : ℝ) / u)
    (hgate : ((p : ℝ) - 1) * ((p : ℝ) - 2) / 2 <
      (N : ℝ) * ((p : ℝ) / k - 1 - ((p : ℝ) - 1) / u)) :
    ((Finset.Icc (L : ℤ) (R : ℤ)).card : ℝ) + (p.choose 2 : ℕ) ≤
      (p : ℝ) * ((N : ℝ) / k -
        (Ground N \ Finset.Icc (L : ℤ) (R : ℤ)).card) := by
  obtain ⟨hI, hext⟩ := actual_interval_ground_card hL hLR hRN
  have hpR : (1 : ℝ) < p := by exact_mod_cast (show 1 < p by omega)
  have hs := central_gate_real hpR hwidth hgate
  rw [hI, hext, Nat.cast_choose_two]
  linarith only [hs]

theorem actual_trace_sum_capacity {ι α : Type*} [DecidableEq ι] [DecidableEq α]
    (Ω : Finset α) (F : Finset ι) (T : ι → Finset α) (p : ℕ) (lower : ℝ)
    (hp : 0 < p) (hground : ∀ S ∈ F, T S ⊆ Ω)
    (hlong : ∀ S ∈ F, lower < ((T S).card : ℝ))
    (hpair : ∀ S ∈ F, ∀ U ∈ F, S ≠ U → ((T S) ∩ (T U)).card ≤ 1)
    (hgate : (Ω.card : ℝ) + (p.choose 2 : ℕ) ≤ p * lower) : F.card ≤ p - 1 := by
  by_contra hn
  have hcount : p ≤ F.card := by omega
  obtain ⟨G, hGF, hGc⟩ := Finset.exists_subset_card_eq hcount
  have hs := TracePacking43.trace_sum_bound G T (fun S hS U hU hSU =>
    hpair S (hGF hS) U (hGF hU) hSU)
  have hsub : G.biUnion T ⊆ Ω := by
    intro x hx
    obtain ⟨S, hS, hxS⟩ := Finset.mem_biUnion.mp hx
    exact hground S (hGF hS) hxS
  have hc := Finset.card_le_card hsub
  have hupper : (∑ S ∈ G, ((T S).card : ℝ)) ≤ (Ω.card : ℝ) + (p.choose 2 : ℕ) := by
    have hn' : (∑ S ∈ G, (T S).card) ≤ Ω.card + p.choose 2 := by
      rw [hGc] at hs
      omega
    exact_mod_cast hn'
  have hne : G.Nonempty := Finset.card_pos.mp (by omega)
  have hsum := Finset.sum_lt_sum_of_nonempty hne (fun S hS => hlong S (hGF hS))
  simp only [Finset.sum_const, nsmul_eq_mul, hGc] at hsum
  nlinarith only [hsum, hupper, hgate]

theorem actual_dense_trace_lower {N : ℕ} {S I : Finset ℤ} {k : ℝ}
    (hk : 0 < k) (hS : S ⊆ Ground N) (hdense : (N : ℝ) < k * S.card) :
    (N : ℝ) / k - (Ground N \ I).card < ((S ∩ I).card : ℝ) := by
  have hsub : S \ I ⊆ Ground N \ I := by
    intro x hx
    obtain ⟨hxS, hxI⟩ := Finset.mem_sdiff.mp hx
    exact Finset.mem_sdiff.mpr ⟨hS hxS, hxI⟩
  have hcount := Finset.card_le_card hsub
  have hcountR : ((S \ I).card : ℝ) ≤ (Ground N \ I).card := by exact_mod_cast hcount
  have he := Finset.card_sdiff_add_card_inter S I
  have heR : ((S \ I).card : ℝ) + (S ∩ I).card = S.card := by exact_mod_cast he
  have hd : (N : ℝ) / k < S.card := (div_lt_iff₀ hk).mpr (by simpa [mul_comm] using hdense)
  linarith only [hd, hcountR, heR]

theorem actual_off_point_capacity {N : ℕ} (F : Finset (Finset ℤ)) (L R : ℤ)
    (d a : Finset ℤ → ℤ) (y : ℤ) (p : ℕ) (k : ℝ)
    (hp : 0 < p) (hk : 0 < k) (hlegal : Legal (Ground N) F)
    (htrace : ∀ S ∈ F, APAt (d S) (a S) (S ∩ Finset.Icc L R))
    (hdense : ∀ S ∈ F, (N : ℝ) < k * S.card)
    (hgate : ((Finset.Icc L R).card : ℝ) + (p.choose 2 : ℕ) ≤
      p * ((N : ℝ) / k - (Ground N \ Finset.Icc L R).card)) :
    (OffPoint F d a y).card ≤ p - 1 := by
  apply actual_trace_sum_capacity (Finset.Icc L R) (OffPoint F d a y)
    (fun S => S ∩ Finset.Icc L R) p
    ((N : ℝ) / k - (Ground N \ Finset.Icc L R).card) hp
  · intro S hS
    exact Finset.inter_subset_right
  · intro S hS
    exact actual_dense_trace_lower hk (hlegal.1 S (Finset.mem_filter.mp hS).1)
      (hdense S (Finset.mem_filter.mp hS).1)
  · intro S hS U hU hSU
    obtain ⟨hSF, hyS, hoff⟩ := Finset.mem_filter.mp hS
    obtain ⟨hUF, hyU, _⟩ := Finset.mem_filter.mp hU
    exact off_point_trace_inter_card (htrace S hSF) (hlegal.2 S hSF U hUF hSU) hyS hyU hoff
  · exact hgate

theorem actual_off_residue_count {N : ℕ} (F : Finset (Finset ℤ)) (L R : ℤ)
    (d a : Finset ℤ → ℤ) (p : ℕ) (k : ℝ)
    (hp : 0 < p) (hk : 0 < k) (hlegal : Legal (Ground N) F)
    (htrace : ∀ S ∈ F, APAt (d S) (a S) (S ∩ Finset.Icc L R))
    (hdense : ∀ S ∈ F, (N : ℝ) < k * S.card)
    (hgate : ((Finset.Icc L R).card : ℝ) + (p.choose 2 : ℕ) ≤
      p * ((N : ℝ) / k - (Ground N \ Finset.Icc L R).card)) :
    (OffMembers F d a).card ≤ (p - 1) * (Ground N \ Finset.Icc L R).card := by
  have hcover : OffMembers F d a ⊆
      (Ground N \ Finset.Icc L R).biUnion (OffPoint F d a) := by
    intro S hS
    obtain ⟨hSF, y, hyS, hoff⟩ := Finset.mem_filter.mp hS
    have hyI : y ∉ Finset.Icc L R := by
      intro hyI
      exact hoff (origin_dvd (htrace S hSF) (Finset.mem_inter.mpr ⟨hyS, hyI⟩))
    exact Finset.mem_biUnion.mpr ⟨y,
      Finset.mem_sdiff.mpr ⟨hlegal.1 S hSF hyS, hyI⟩,
      Finset.mem_filter.mpr ⟨hSF, hyS, hoff⟩⟩
  calc
    _ ≤ ((Ground N \ Finset.Icc L R).biUnion (OffPoint F d a)).card :=
      Finset.card_le_card hcover
    _ ≤ ∑ y ∈ Ground N \ Finset.Icc L R, (OffPoint F d a y).card := Finset.card_biUnion_le
    _ ≤ ∑ _y ∈ Ground N \ Finset.Icc L R, (p - 1) := Finset.sum_le_sum (by
      intro y _
      exact actual_off_point_capacity F L R d a y p k hp hk hlegal htrace hdense hgate)
    _ = (p - 1) * (Ground N \ Finset.Icc L R).card := by simp [Nat.mul_comm]

theorem actual_off_residue_width {N L R p : ℕ} {k u : ℝ}
    (F : Finset (Finset ℤ)) (d a : Finset ℤ → ℤ)
    (hL : 1 ≤ L) (hLR : L ≤ R) (hRN : R ≤ N) (hp : 2 ≤ p) (hk : 0 < k)
    (hlegal : Legal (Ground N) F)
    (htrace : ∀ S ∈ F, APAt (d S) (a S) (S ∩ Finset.Icc (L : ℤ) (R : ℤ)))
    (hdense : ∀ S ∈ F, (N : ℝ) < k * S.card)
    (hwidth : (L : ℝ) + (N - R) < (N : ℝ) / u)
    (hgate : ((p : ℝ) - 1) * ((p : ℝ) - 2) / 2 <
      (N : ℝ) * ((p : ℝ) / k - 1 - ((p : ℝ) - 1) / u)) :
    ((OffMembers F d a).card : ℝ) ≤ ((p : ℝ) - 1) *
      ((L : ℝ) + (N - R) - 1) := by
  have hactual := actual_central_gate hL hLR hRN hp hwidth hgate
  have hc := actual_off_residue_count F (L : ℤ) (R : ℤ) d a p k
    (by omega) hk hlegal htrace hdense hactual
  have hcR : ((OffMembers F d a).card : ℝ) ≤
      ((p - 1 : ℕ) : ℝ) * (Ground N \ Finset.Icc (L : ℤ) (R : ℤ)).card := by
    exact_mod_cast hc
  rw [Nat.cast_sub (by omega : 1 ≤ p), Nat.cast_one,
    (actual_interval_ground_card hL hLR hRN).2] at hcR
  exact hcR

def ActualOffPoints (S : Finset ℤ) (d a : ℤ) : Finset ℤ :=
  S.filter (fun y => ¬ d ∣ y - a)

def HeavyOffMembers (F : Finset (Finset ℤ)) (d a : Finset ℤ → ℤ)
    (threshold : ℝ) : Finset (Finset ℤ) :=
  F.filter (fun S => threshold < ((ActualOffPoints S (d S) (a S)).card : ℝ))

/-- Pay every actual off point before counting sources with many of them.
The relation is the incidence of the original member with its own residue
class; replacing the residue class or using the trace's complement would
change this statement. -/
theorem actual_heavy_off_incidence {N : ℕ} (F : Finset (Finset ℤ)) (L R : ℤ)
    (d a : Finset ℤ → ℤ) (p : ℕ) (k threshold : ℝ)
    (hp : 0 < p) (hk : 0 < k) (hlegal : Legal (Ground N) F)
    (htrace : ∀ S ∈ F, APAt (d S) (a S) (S ∩ Finset.Icc L R))
    (hdense : ∀ S ∈ F, (N : ℝ) < k * S.card)
    (hgate : ((Finset.Icc L R).card : ℝ) + (p.choose 2 : ℕ) ≤
      p * ((N : ℝ) / k - (Ground N \ Finset.Icc L R).card)) :
    ((HeavyOffMembers F d a threshold).card : ℝ) * threshold ≤
      ((p - 1 : ℕ) : ℝ) * (Ground N \ Finset.Icc L R).card := by
  let H := HeavyOffMembers F d a threshold
  let Ω := Ground N \ Finset.Icc L R
  let rel : Finset ℤ → ℤ → Prop := fun S y => y ∈ S ∧ ¬ d S ∣ y - a S
  have hHF : H ⊆ F := Finset.filter_subset _ _
  have hHlegal : Legal (Ground N) H :=
    ⟨fun S hS => hlegal.1 S (hHF hS),
     fun S hS T hT hST => hlegal.2 S (hHF hS) T (hHF hT) hST⟩
  have habove : ∀ S ∈ H,
      Ω.bipartiteAbove rel S = ActualOffPoints S (d S) (a S) := by
    intro S hS
    ext y
    simp only [Finset.mem_bipartiteAbove, ActualOffPoints, Finset.mem_filter, rel]
    constructor
    · rintro ⟨_, hyS, hoff⟩
      exact ⟨hyS, hoff⟩
    · rintro ⟨hyS, hoff⟩
      have hyI : y ∉ Finset.Icc L R := by
        intro hyI
        exact hoff (origin_dvd (htrace S (hHF hS)) (Finset.mem_inter.mpr ⟨hyS, hyI⟩))
      exact ⟨Finset.mem_sdiff.mpr ⟨hlegal.1 S (hHF hS) hyS, hyI⟩, hyS, hoff⟩
  have hsupply : ∀ S ∈ H, threshold ≤ (Ω.bipartiteAbove rel S).card := by
    intro S hS
    rw [habove S hS]
    exact (Finset.mem_filter.mp hS).2.le
  have hcapacity : ∀ y ∈ Ω,
      ((H.bipartiteBelow rel y).card : ℝ) ≤ ((p - 1 : ℕ) : ℝ) := by
    intro y _hy
    have heq : H.bipartiteBelow rel y = OffPoint H d a y := rfl
    rw [heq]
    exact_mod_cast actual_off_point_capacity H L R d a y p k hp hk hHlegal
      (fun S hS => htrace S (hHF hS)) (fun S hS => hdense S (hHF hS)) hgate
  have hb := Finset.card_nsmul_le_card_nsmul (R := ℝ) (r := rel)
    (s := H) (t := Ω) hsupply hcapacity
  simp only [nsmul_eq_mul] at hb
  simpa only [H, Ω, mul_comm] using hb

theorem actual_heavy_off_count904 {N L R : ℕ} (F : Finset (Finset ℤ))
    (d a : Finset ℤ → ℤ) (hN : 656184 ≤ N)
    (hL : 1 ≤ L) (hLR : L ≤ R) (hRN : R ≤ N)
    (hlegal : Legal (Ground N) F)
    (htrace : ∀ S ∈ F, APAt (d S) (a S) (S ∩ Finset.Icc (L : ℤ) (R : ℤ)))
    (hdense : ∀ S ∈ F, (N : ℝ) < 11 * S.card)
    (hwidth : (L : ℝ) + (N - R) < (N : ℝ) / (2951 / 100 : ℝ)) :
    (HeavyOffMembers F d a ((3 / 5000 : ℝ) * N)).card ≤ 904 := by
  have hnR : (656184 : ℝ) ≤ N := by exact_mod_cast hN
  have hgate : (16 : ℝ) * 15 / 2 <
      (N : ℝ) * ((17 : ℝ) / 11 - 1 - 16 / (2951 / 100 : ℝ)) := by
    norm_num
    nlinarith only [hnR]
  have hactual := actual_central_gate (p := 17) (k := 11) hL hLR hRN (by omega)
    hwidth (by convert hgate using 1 <;> norm_num)
  have hb := actual_heavy_off_incidence F (L : ℤ) (R : ℤ) d a 17 11
    ((3 / 5000 : ℝ) * N) (by omega) (by norm_num) hlegal htrace hdense hactual
  rw [(actual_interval_ground_card hL hLR hRN).2] at hb
  norm_num only [Nat.reduceSub, Nat.cast_ofNat] at hb
  by_contra hh
  have hlarge : (905 : ℝ) ≤
      (HeavyOffMembers F d a ((3 / 5000 : ℝ) * N)).card := by
    exact_mod_cast (show 905 ≤ (HeavyOffMembers F d a ((3 / 5000 : ℝ) * N)).card by omega)
  have hm := mul_le_mul_of_nonneg_right hlarge
    (show (0 : ℝ) ≤ (3 / 5000 : ℝ) * N by positivity)
  nlinarith only [hb, hm, hwidth, hnR]

/-- A member with few off points cannot have a large true trace step.
The on-class points are bounded by the full residue class in the actual
ground set; the member itself need not fill that class. -/
theorem actual_few_off_step_le11 {N : ℕ} {S : Finset ℤ} {d a : ℤ}
    (hN : 656184 ≤ N) (hS : S ⊆ Ground N) (hd : 0 < d)
    (hdense : (N : ℝ) < 11 * S.card)
    (hfew : ((ActualOffPoints S d a).card : ℝ) ≤ (3 / 5000 : ℝ) * N) :
    d ≤ 11 := by
  by_contra hh
  have hd12 : (12 : ℤ) ≤ d := by omega
  have hd12R : (12 : ℝ) ≤ d := by exact_mod_cast hd12
  let C := (Ground N).filter (fun y => d ∣ y - a)
  have hclass : APAt d a C := by
    refine ⟨hd, 1, (N : ℤ), ?_⟩
    intro y
    simp only [C, Finset.mem_filter]
    rw [mem_ground]
    tauto
  have hC : (C.card : ℝ) ≤ (N : ℝ) / 12 + 1 := by
    by_cases hne : C.Nonempty
    · have hground : C ⊆ Finset.Icc 1 (N : ℤ) := by
        intro y hy
        exact Finset.mem_Icc.mpr ((mem_ground N y).mp (Finset.mem_filter.mp hy).1)
      have hs := apAt_card_span hclass hne hground
      have hsR : (d : ℝ) * ((C.card : ℝ) - 1) ≤ (N : ℝ) - 1 := by exact_mod_cast hs
      have hcR : (1 : ℝ) ≤ C.card := by
        exact_mod_cast (show 1 ≤ C.card from Finset.card_pos.mpr hne)
      have hm := mul_le_mul_of_nonneg_right hd12R (sub_nonneg.mpr hcR)
      nlinarith only [hsR, hm]
    · have he : C = ∅ := Finset.not_nonempty_iff_eq_empty.mp hne
      rw [he]
      simp only [Finset.card_empty, Nat.cast_zero]
      positivity
  let A := S.filter (fun y => d ∣ y - a)
  have hAC : A ⊆ C := by
    intro y hy
    obtain ⟨hyS, hyclass⟩ := Finset.mem_filter.mp hy
    exact Finset.mem_filter.mpr ⟨hS hyS, hyclass⟩
  have hA : (A.card : ℝ) ≤ C.card := by exact_mod_cast Finset.card_le_card hAC
  have hpart := Finset.card_filter_add_card_filter_not (s := S) (fun y => d ∣ y - a)
  have hpartR : (A.card : ℝ) + (ActualOffPoints S d a).card = S.card := by
    exact_mod_cast hpart
  have hnR : (656184 : ℝ) ≤ N := by exact_mod_cast hN
  nlinarith only [hdense, hfew, hC, hA, hpartR, hnR]

theorem actual_few_positive_off_step_range {N : ℕ} {S : Finset ℤ} {d a : ℤ}
    (hN : 656184 ≤ N) (hS : S ⊆ Ground N) (hd : 0 < d)
    (hdense : (N : ℝ) < 11 * S.card)
    (hfew : ((ActualOffPoints S d a).card : ℝ) ≤ (3 / 5000 : ℝ) * N)
    (hpositive : 0 < (ActualOffPoints S d a).card) : 2 ≤ d ∧ d ≤ 11 := by
  have hu := actual_few_off_step_le11 hN hS hd hdense hfew
  refine ⟨?_, hu⟩
  by_contra hh
  have he : d = 1 := by omega
  simp [ActualOffPoints, he] at hpositive

#print axioms actual_dense_trace_lower
#print axioms actual_interval_ground_card
#print axioms actual_central_gate
#print axioms actual_off_point_capacity
#print axioms actual_off_residue_count
#print axioms actual_off_residue_width
#print axioms actual_heavy_off_incidence
#print axioms actual_heavy_off_count904
#print axioms actual_few_off_step_le11
#print axioms actual_few_positive_off_step_range
end
end JSP233.ActualGrid212
