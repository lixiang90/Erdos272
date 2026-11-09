module

public import Erdos272.Core.N200000.CoreNormal200000

@[expose] public section

/-! Pure integer index-pair certificates map injectively to actual core
pairs. Their exceptional interval is one shared interval in the core. -/
namespace JSP233.IndexedCorePairs200000
open StarCompletion APGeometry SourceBridge208 NearAP36 IntrinsicTriples208
open ActualRun200000 RunTrace200000 CorePairHull200000 PairPool200000 CoreNormal200000
open scoped Classical BigOperators
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 0

def Primitive (h : ℕ) (ell : ℤ) (Q : Finset ℕ) : Prop :=
  ∀ i ∈ Q, ∀ j ∈ Q, i < j → Int.gcd ((j : ℤ) - i) (ell - (h : ℤ) * i) = 1

def GoodIndex (a h : ℕ) (ell : ℤ) (J : Finset ℕ) : Finset (Finset ℕ) :=
  ((Finset.range a).powersetCard 2).filter (fun Q => ¬Q ⊆ J ∧ Primitive h ell Q)

def Lift (p d : ℤ) (Q : Finset ℕ) : Finset ℤ := Q.image (fun i : ℕ => p + d * (i : ℤ))

def ExceptionLength (a h : ℕ) : ℕ := if h = 1 then 0 else min a ((a + h - 1) / h)

theorem point_injective {p d : ℤ} (hd : 0 < d) : Function.Injective (fun i : ℕ => p + d * (i : ℤ)) := by
  intro i j he
  have hij : (i : ℤ) = j := by nlinarith
  exact_mod_cast hij

theorem sorted_index_pair {Q : Finset ℕ} (hQ : Q.card = 2) : ∃ i j : ℕ, i < j ∧ Q = {i, j} := by
  obtain ⟨i, j, hne, hpair⟩ := Finset.card_eq_two.mp hQ
  by_cases hij : i < j
  · exact ⟨i, j, hij, hpair⟩
  · exact ⟨j, i, by omega, hpair.trans (Finset.pair_comm _ _)⟩

theorem good_index_data {a h : ℕ} {ell : ℤ} {Q J : Finset ℕ} (hQ : Q ∈ GoodIndex a h ell J) :
    Q ⊆ Finset.range a ∧ Q.card = 2 ∧ ¬Q ⊆ J ∧ Primitive h ell Q := by
  obtain ⟨hpow, hnot, hprim⟩ := Finset.mem_filter.mp hQ
  obtain ⟨hsub, hcard⟩ := Finset.mem_powersetCard.mp hpow
  exact ⟨hsub, hcard, hnot, hprim⟩

theorem actual_lift_good_pair {S P : Finset ℤ} {p d x : ℤ} {a : ℕ} {Q J : Finset ℕ}
    (hd : 0 < d) (hP : MaximalAPCore S P) (hAt : APAt d p P)
    (hgrid : P = (Finset.range a).image (fun i : ℕ => p + d * (i : ℤ))) (hx : x ∈ S \ P)
    (n : Normalization d (x - p)) (hbranch : n.h = 1 ∨ Trace a p d (Run S n.g x) ⊆ J)
    (hQ : Q ∈ GoodIndex a n.h n.ell J) : Lift p d Q ∈ GoodPairs S P x := by
  obtain ⟨hsub, hcard, hnot, hprim⟩ := good_index_data hQ
  have hpoints : ∀ k < a, p + d * (k : ℤ) ∈ P := by
    intro k hk
    rw [hgrid]
    exact Finset.mem_image.mpr ⟨k, Finset.mem_range.mpr hk, rfl⟩
  have hLiftSub : Lift p d Q ⊆ P := by
    intro z hz
    obtain ⟨k, hk, rfl⟩ := Finset.mem_image.mp hz
    exact hpoints k (Finset.mem_range.mp (hsub hk))
  have hLiftCard : (Lift p d Q).card = 2 := by
    rw [Lift, Finset.card_image_of_injective _ (point_injective hd), hcard]
  apply Finset.mem_filter.mpr
  refine ⟨Finset.mem_powersetCard.mpr ⟨hLiftSub, hLiftCard⟩, ?_⟩
  obtain ⟨i, j, hij, hpair⟩ := sorted_index_pair hcard
  have hiQ : i ∈ Q := by rw [hpair]; simp
  have hjQ : j ∈ Q := by rw [hpair]; simp
  have hi : i < a := Finset.mem_range.mp (hsub hiQ)
  have hj : j < a := Finset.mem_range.mp (hsub hjQ)
  have hgeq := normalized_pair_gcd n (i : ℤ) (j : ℤ) (hprim i hiQ j hjQ hij)
  have hab : p + d * (i : ℤ) < p + d * (j : ℤ) := by
    have hZ : (i : ℤ) < j := by exact_mod_cast hij
    nlinarith only [hd, hZ]
  have hpool : ({x, p + d * (i : ℤ), p + d * (j : ℤ)} : Finset ℤ) ∈ Pool S := by
    rcases hbranch with hone | htrace
    · have hgd : n.g = d := by simpa only [hone, Nat.cast_one, one_mul] using n.step_eq.symm
      exact same_phase_pool hP hAt hx (hpoints i hi) (hpoints j hj) hab (hgeq.trans hgd)
    · have hmiss : ¬ (i ∈ J ∧ j ∈ J) := by
        intro hh
        apply hnot
        rw [hpair]
        exact Finset.insert_subset_iff.mpr ⟨hh.1, Finset.singleton_subset_iff.mpr hh.2⟩
      exact outside_padded_trace_pool hd hi hj hij (Finset.mem_sdiff.mp hx).1
        (fun k hk => hP.1 (hpoints k hk)) (fun k hk he => (Finset.mem_sdiff.mp hx).2 (he ▸ hpoints k hk))
        htrace hmiss hgeq
  simpa only [Lift, hpair, Finset.image_insert, Finset.image_singleton] using hpool

theorem actual_index_pair_count {S P : Finset ℤ} {p d x : ℤ} {a : ℕ} {J : Finset ℕ}
    (hd : 0 < d) (hP : MaximalAPCore S P) (hAt : APAt d p P)
    (hgrid : P = (Finset.range a).image (fun i : ℕ => p + d * (i : ℤ))) (hx : x ∈ S \ P)
    (n : Normalization d (x - p)) (hbranch : n.h = 1 ∨ Trace a p d (Run S n.g x) ⊆ J) :
    (GoodIndex a n.h n.ell J).card ≤ (GoodPairs S P x).card := by
  apply Finset.card_le_card_of_injOn (Lift p d)
  · intro Q hQ
    exact actual_lift_good_pair hd hP hAt hgrid hx n hbranch hQ
  · exact (Finset.image_injective (point_injective hd)).injOn

#print axioms point_injective
#print axioms sorted_index_pair
#print axioms good_index_data
#print axioms actual_lift_good_pair
#print axioms actual_index_pair_count
end
end JSP233.IndexedCorePairs200000
