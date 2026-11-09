module

public import Erdos272.Resources.PairSlice208

@[expose] public section

/-! Actual rank-one, rank-two and rank-three pair covers. -/
namespace JSP233.PairRanks208
open StarCompletion APGeometry SourceBridge208 PairEnvelope208 PairSlice208
open scoped Classical
noncomputable section
set_option maxHeartbeats 0

def Level (S : Finset ℤ) (a b : ℤ) (q : ℕ) : Finset ℤ :=
  if (q : ℤ) ∣ b-a then Envelope S ((b-a)/q) a b else ∅

def CoveredPoints (S : Finset ℤ) (a b : ℤ) : Finset ℤ :=
  S.filter fun x => ∃ R : Finset ℤ, IsAP R ∧ R ⊆ S ∧ a ∈ R ∧ b ∈ R ∧ x ∈ R

def IntrinsicPoints (S : Finset ℤ) (a b : ℤ) : Finset ℤ := S \ CoveredPoints S a b

@[simp] theorem level_one (S : Finset ℤ) (a b : ℤ) :
    Level S a b 1 = Envelope S (b-a) a b := by simp [Level]

theorem cover_code {S R : Finset ℤ} {a b : ℤ}
    (hRS : R ⊆ S) (hR : IsAP R) (ha : a ∈ R) (hb : b ∈ R) (hab : a < b) :
    ∃ q : ℕ, 0 < q ∧ q ≤ Rank S a b ∧ (q : ℤ) ∣ b-a ∧
      APAt ((b-a)/q) a R := by
  obtain ⟨d, p, hAP, _⟩ := (isAP_iff_exists_APAt R).mp hR
  have hRa := apAt_rebase hAP ha
  have hd := hAP.1
  obtain ⟨k, hk⟩ := apAt_dvd_sub hRa ha hb
  have hk0 : 0 < k := by nlinarith
  let q := k.toNat
  have hq : (q : ℤ) = k := Int.toNat_of_nonneg hk0.le
  have hq0 : 0 < q := by omega
  have hD : b-a = d*q := by rw [hq]; exact hk
  refine ⟨q, hq0, subdivisions_le_rank hRS hRa ha hb hab hD, ⟨d, by nlinarith only [hD]⟩, ?_⟩
  have he : (b-a)/(q : ℤ) = d := by rw [hD]; exact Int.mul_ediv_cancel _ (by omega)
  rw [he]
  exact hRa

theorem covered_level {S : Finset ℤ} {a b x : ℤ} (hab : a < b)
    (hx : x ∈ CoveredPoints S a b) :
    ∃ q : ℕ, 0 < q ∧ q ≤ Rank S a b ∧ x ∈ Level S a b q := by
  obtain ⟨_, R, hR, hRS, ha, hb, hxR⟩ := Finset.mem_filter.mp hx
  obtain ⟨q, hq, hqr, hdiv, hRa⟩ := cover_code hRS hR ha hb hab
  refine ⟨q, hq, hqr, ?_⟩
  rw [Level, if_pos hdiv]
  exact cover_subset_envelope hRS hRa ha hb hxR

theorem level_extra (S : Finset ℤ) {a b : ℤ} (hab : a < b) {q : ℕ} (hq : 0 < q) :
    (Level S a b q \ Envelope S (b-a) a b).card ≤ MaxAPSize S-MaxAPSize S/q := by
  by_cases hdiv : (q : ℤ) ∣ b-a
  · rw [Level, if_pos hdiv]
    by_cases hne : (Covers S ((b-a)/q) a b).Nonempty
    · obtain ⟨R, hR⟩ := hne
      obtain ⟨hRS, hRa, ha, hb⟩ := mem_covers.mp hR
      have hsub := cover_subset_envelope hRS hRa ha hb
      apply extra_card (envelope_subset S _ a b) (envelope_APAt hRS hRa ha hb)
        (hsub ha) (hsub hb) hab (Int.ediv_mul_cancel hdiv).symm hq
      exact envelope_card_le_max hRS hRa ha hb
    · have he : Covers S ((b-a)/q) a b = ∅ := Finset.not_nonempty_iff_eq_empty.mp hne
      simp only [Envelope, he, Finset.biUnion_empty, Finset.empty_sdiff, Finset.card_empty, zero_le]
  · simp only [Level, if_neg hdiv, Finset.empty_sdiff, Finset.card_empty, zero_le]

theorem level_positive {S : Finset ℤ} {a b : ℤ} {q : ℕ}
    (hne : (Level S a b q).Nonempty) :
    (q : ℤ) ∣ b-a ∧ ∃ R : Finset ℤ, R ⊆ S ∧ APAt ((b-a)/q) a R ∧ a ∈ R ∧ b ∈ R := by
  by_cases hdiv : (q : ℤ) ∣ b-a
  · refine ⟨hdiv, ?_⟩
    rw [Level, if_pos hdiv] at hne
    obtain ⟨x, hx⟩ := hne
    obtain ⟨R, hRS, hR, ha, hb, _⟩ := mem_envelope.mp hx
    exact ⟨R, hRS, hR, ha, hb⟩
  · simp only [Level, if_neg hdiv, Finset.not_nonempty_empty] at hne

theorem incompatible_two_three {S : Finset ℤ} {a b : ℤ} (hab : a < b)
    (hrank : Rank S a b ≤ 3) :
    ¬ ((Level S a b 2).Nonempty ∧ (Level S a b 3).Nonempty) := by
  rintro ⟨h2, h3⟩
  obtain ⟨hd2, R, hRS, hR, haR, hbR⟩ := level_positive h2
  obtain ⟨hd3, T, hTS, hT, haT, hbT⟩ := level_positive h3
  let d := (b-a)/2
  let f := (b-a)/3
  have hd : 0 < d := hR.1
  have hf : 0 < f := hT.1
  have hD2 : b-a = d*2 := (Int.ediv_mul_cancel hd2).symm
  have hD3 : b-a = f*3 := (Int.ediv_mul_cancel hd3).symm
  have hm : a+d ∈ S := hRS (apAt_fill hR haR hbR (by omega) (by omega)
    ⟨1, by change a+d-a=d*1; ring⟩)
  have h1 : a+f ∈ S := hTS (apAt_fill hT haT hbT (by omega) (by omega)
    ⟨1, by change a+f-a=f*1; ring⟩)
  have h2 : a+2*f ∈ S := hTS (apAt_fill hT haT hbT (by omega) (by omega)
    ⟨2, by change a+2*f-a=f*2; ring⟩)
  have horder : a+f < a+d ∧ a+d < a+2*f := by omega
  let V : Finset ℤ := {a+f, a+d, a+2*f}
  have hVcard : V.card = 3 := by
    dsimp only [V]
    rw [Finset.card_insert_of_notMem (by
      simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
      exact ⟨by omega, by omega⟩), Finset.card_pair (by omega)]
  have hVsub : V ⊆ S.filter fun x => a < x ∧ x < b := by
    intro x hx
    simp only [V, Finset.mem_insert, Finset.mem_singleton] at hx
    rcases hx with rfl | rfl | rfl <;> apply Finset.mem_filter.mpr
    · exact ⟨h1, by omega, by omega⟩
    · exact ⟨hm, by omega, by omega⟩
    · exact ⟨h2, by omega, by omega⟩
  have hc := Finset.card_le_card hVsub
  unfold Rank at hrank
  omega

theorem covered_rank_one {S : Finset ℤ} {a b : ℤ} (hab : a < b)
    (hrank : Rank S a b ≤ 1) : CoveredPoints S a b ⊆ Envelope S (b-a) a b := by
  intro x hx
  obtain ⟨q, hq, hqr, hxq⟩ := covered_level hab hx
  have he : q = 1 := by omega
  simpa only [he, level_one] using hxq

theorem covered_rank_two {S : Finset ℤ} {a b : ℤ} (hab : a < b)
    (hrank : Rank S a b ≤ 2) :
    CoveredPoints S a b ⊆ Envelope S (b-a) a b ∪ Level S a b 2 := by
  intro x hx
  obtain ⟨q, hq, hqr, hxq⟩ := covered_level hab hx
  have he : q = 1 ∨ q = 2 := by omega
  rcases he with rfl | rfl
  · exact Finset.mem_union_left _ (by simpa only [level_one] using hxq)
  · exact Finset.mem_union_right _ hxq

theorem covered_rank_three {S : Finset ℤ} {a b : ℤ} (hab : a < b)
    (hrank : Rank S a b ≤ 3) :
    ∃ q ∈ ({2,3} : Finset ℕ),
      CoveredPoints S a b ⊆ Envelope S (b-a) a b ∪ Level S a b q := by
  by_cases h2 : (Level S a b 2).Nonempty
  · have h3 : Level S a b 3 = ∅ := Finset.not_nonempty_iff_eq_empty.mp
      (fun hh => incompatible_two_three hab hrank ⟨h2, hh⟩)
    refine ⟨2, by simp, ?_⟩
    intro x hx
    obtain ⟨q, hq, hqr, hxq⟩ := covered_level hab hx
    have he : q = 1 ∨ q = 2 ∨ q = 3 := by omega
    rcases he with rfl | rfl | rfl
    · exact Finset.mem_union_left _ (by simpa only [level_one] using hxq)
    · exact Finset.mem_union_right _ hxq
    · simp only [h3, Finset.notMem_empty] at hxq
  · have he2 : Level S a b 2 = ∅ := Finset.not_nonempty_iff_eq_empty.mp h2
    refine ⟨3, by simp, ?_⟩
    intro x hx
    obtain ⟨q, hq, hqr, hxq⟩ := covered_level hab hx
    have he : q = 1 ∨ q = 2 ∨ q = 3 := by omega
    rcases he with rfl | rfl | rfl
    · exact Finset.mem_union_left _ (by simpa only [level_one] using hxq)
    · simp only [he2, Finset.notMem_empty] at hxq
    · exact Finset.mem_union_right _ hxq

#print axioms cover_code
#print axioms incompatible_two_three
#print axioms covered_rank_three
end
end JSP233.PairRanks208
