module

public import Erdos272.Resources.SourceBridge208
public import Erdos272.Foundation.APGeometry
public import Erdos272.Foundation.ProofTactics

@[expose] public section

/-! Actual unions of all fixed-step AP covers of one pair. -/
namespace JSP233.PairEnvelope208
open StarCompletion APGeometry SourceBridge208
open scoped Classical BigOperators
noncomputable section
set_option maxHeartbeats 0

def Covers (S : Finset ℤ) (d a b : ℤ) : Finset (Finset ℤ) :=
  S.powerset.filter fun R => APAt d a R ∧ a ∈ R ∧ b ∈ R

def Envelope (S : Finset ℤ) (d a b : ℤ) : Finset ℤ :=
  (Covers S d a b).biUnion id

theorem mem_covers {S R : Finset ℤ} {d a b : ℤ} :
    R ∈ Covers S d a b ↔ R ⊆ S ∧ APAt d a R ∧ a ∈ R ∧ b ∈ R := by
  simp only [Covers, Finset.mem_filter, Finset.mem_powerset]

theorem mem_envelope {S : Finset ℤ} {d a b x : ℤ} :
    x ∈ Envelope S d a b ↔
      ∃ R : Finset ℤ, R ⊆ S ∧ APAt d a R ∧ a ∈ R ∧ b ∈ R ∧ x ∈ R := by
  simp only [Envelope, Finset.mem_biUnion, id_eq, mem_covers]
  aesop

theorem envelope_subset (S : Finset ℤ) (d a b : ℤ) : Envelope S d a b ⊆ S := by
  intro x hx
  obtain ⟨R, hRS, _, _, _, hxR⟩ := mem_envelope.mp hx
  exact hRS hxR

theorem union_same_step {U V : Finset ℤ} {d a : ℤ}
    (hU : APAt d a U) (hV : APAt d a V) (haU : a ∈ U) (haV : a ∈ V) :
    APAt d a (U ∪ V) := by
  simpa only [APAt, Finset.mem_union] using
    PrivateUnion.union_APAt d a (fun x => x ∈ U) (fun x => x ∈ V) hU hV haU haV

theorem biUnion_same_step {H : Finset (Finset ℤ)} {d a : ℤ} (hne : H.Nonempty)
    (hH : ∀ R ∈ H, APAt d a R ∧ a ∈ R) : APAt d a (H.biUnion id) := by
  induction H using Finset.induction_on with
  | empty => simp at hne
  | @insert R H hnot ih =>
    have hR := hH R (Finset.mem_insert_self R H)
    by_cases hempty : H = ∅
    · subst H
      simpa using hR.1
    · have hH' : H.Nonempty := Finset.nonempty_iff_ne_empty.mpr hempty
      have ht : APAt d a (H.biUnion id) := ih hH' (fun U hU => hH U (Finset.mem_insert_of_mem hU))
      have ha : a ∈ H.biUnion id := by
        obtain ⟨U, hU⟩ := hH'
        exact Finset.mem_biUnion.mpr ⟨U, hU, (hH U (Finset.mem_insert_of_mem hU)).2⟩
      simpa only [Finset.biUnion_insert, id_eq] using union_same_step hR.1 ht hR.2 ha

theorem envelope_APAt {S R : Finset ℤ} {d a b : ℤ}
    (hRS : R ⊆ S) (hR : APAt d a R) (ha : a ∈ R) (hb : b ∈ R) :
    APAt d a (Envelope S d a b) := by
  apply biUnion_same_step (H := Covers S d a b)
  · exact ⟨R, mem_covers.mpr ⟨hRS, hR, ha, hb⟩⟩
  · intro U hU
    have hh := mem_covers.mp hU
    exact ⟨hh.2.1, hh.2.2.1⟩

theorem cover_subset_envelope {S R : Finset ℤ} {d a b : ℤ}
    (hRS : R ⊆ S) (hR : APAt d a R) (ha : a ∈ R) (hb : b ∈ R) :
    R ⊆ Envelope S d a b := by
  intro x hx
  exact mem_envelope.mpr ⟨R, hRS, hR, ha, hb, hx⟩

theorem envelope_card_le_max {S R : Finset ℤ} {d a b : ℤ}
    (hRS : R ⊆ S) (hR : APAt d a R) (ha : a ∈ R) (hb : b ∈ R) :
    (Envelope S d a b).card ≤ MaxAPSize S := by
  apply AP_card_le_max
    ((isAP_iff_exists_APAt _).mpr ⟨d, a, envelope_APAt hRS hR ha hb,
      cover_subset_envelope hRS hR ha hb ha⟩)
  exact envelope_subset S d a b

theorem pair_APAt {a b : ℤ} (hab : a < b) : APAt (b-a) a ({a,b} : Finset ℤ) := by
  refine ⟨by omega, a, b, ?_⟩
  intro x
  constructor
  · intro hx
    rcases (by simpa only [Finset.mem_insert, Finset.mem_singleton] using hx : x=a ∨ x=b) with rfl | rfl
    · exact ⟨le_rfl, hab.le, by simp⟩
    · exact ⟨hab.le, le_rfl, dvd_refl _⟩
  · rintro ⟨hax, hxb, k, hk⟩
    have hk0 : 0 ≤ k := by nlinarith
    have hk1 : k ≤ 1 := by nlinarith
    have he : k = 0 ∨ k = 1 := by omega
    rcases he with rfl | rfl <;> simp only [mul_zero, mul_one] at hk <;>
      simp only [Finset.mem_insert, Finset.mem_singleton] <;> omega

theorem coarse_APAt {S : Finset ℤ} {a b : ℤ}
    (ha : a ∈ S) (hb : b ∈ S) (hab : a < b) :
    APAt (b-a) a (Envelope S (b-a) a b) :=
  envelope_APAt (by
      intro x hx
      rcases (by simpa only [Finset.mem_insert, Finset.mem_singleton] using hx : x=a ∨ x=b) with rfl | rfl <;> assumption)
    (pair_APAt hab) (by simp) (by simp)

def Rank (S : Finset ℤ) (a b : ℤ) : ℕ :=
  (S.filter fun x => a < x ∧ x < b).card + 1

/-- Every positive-step cover uses no more subdivisions than the actual
rank distance of the pair, since all intermediate lattice points lie in S. -/
theorem subdivisions_le_rank {S R : Finset ℤ} {a b d : ℤ} {q : ℕ}
    (hRS : R ⊆ S) (hR : APAt d a R) (ha : a ∈ R) (hb : b ∈ R)
    (hab : a < b) (hD : b-a = d*q) : q ≤ Rank S a b := by
  have hd : 0 < d := hR.1
  have hq0 : 0 < q := by
    by_contra hh
    have hq : q = 0 := by omega
    rw [hq] at hD
    norm_num at hD
    omega
  let f : ℕ → ℤ := fun j => a + d * (j+1)
  have hinj : Function.Injective f := by
    intro j k he
    dsimp only [f] at he
    have hh : (j : ℤ) = k := by push_cast at he; nlinarith
    exact_mod_cast hh
  have hsub : (Finset.range (q-1)).image f ⊆ S.filter fun x => a < x ∧ x < b := by
    intro x hx
    obtain ⟨j, hj, rfl⟩ := Finset.mem_image.mp hx
    have hjq : j+1 < q := by have := Finset.mem_range.mp hj; omega
    have hjZ : (j+1 : ℕ) < (q : ℤ) := by exact_mod_cast hjq
    have hj0 : (0 : ℤ) < (j+1 : ℕ) := by positivity
    apply Finset.mem_filter.mpr
    have hlo : a < f j := by dsimp only [f]; nlinarith
    have hhi : f j < b := by dsimp only [f]; nlinarith
    exact ⟨hRS (apAt_fill hR ha hb hlo.le hhi.le ⟨(j+1 : ℕ), by dsimp only [f]; push_cast; ring⟩),
      hlo, hhi⟩
  have hc := Finset.card_le_card hsub
  rw [Finset.card_image_of_injective _ hinj, Finset.card_range] at hc
  unfold Rank
  omega

def CoarseSlice (U : Finset ℤ) (D a : ℤ) : Finset ℤ := U.filter fun x => D ∣ x-a

theorem coarseSlice_APAt {U : Finset ℤ} {d D a : ℤ}
    (hU : APAt d a U) (hD : 0 < D) (hdD : d ∣ D) :
    APAt D a (CoarseSlice U D a) := by
  obtain ⟨_, lo, hi, hr⟩ := hU
  refine ⟨hD, lo, hi, ?_⟩
  intro x
  simp only [CoarseSlice, Finset.mem_filter, hr]
  constructor
  · tauto
  · intro hx
    exact ⟨⟨hx.1, hx.2.1, hdD.trans hx.2.2⟩, hx.2.2⟩

theorem coarseSlice_subset_envelope {S U : Finset ℤ} {a b d : ℤ} {q : ℕ}
    (hUS : U ⊆ S) (hU : APAt d a U) (ha : a ∈ U) (hb : b ∈ U)
    (hab : a < b) (hD : b-a = d*q) :
    CoarseSlice U (b-a) a ⊆ Envelope S (b-a) a b := by
  apply cover_subset_envelope
    (by intro x hx; exact hUS (Finset.mem_filter.mp hx).1)
    (coarseSlice_APAt hU (by omega) ⟨q, hD⟩)
  · exact Finset.mem_filter.mpr ⟨ha, by simp⟩
  · exact Finset.mem_filter.mpr ⟨hb, dvd_refl _⟩

#print axioms envelope_APAt
#print axioms subdivisions_le_rank
#print axioms coarseSlice_subset_envelope
end
end JSP233.PairEnvelope208
