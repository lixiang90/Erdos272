module

public import Erdos272.Resources.CoreDensity208
public import Mathlib.Data.Finset.Prod

@[expose] public section

/-! A proper refinement of an AP fills p-1 genuinely new points in every
coarse gap. Both alternatives of the frozen unit block gate are proved from
actual sets and maximum AP cardinality. -/
namespace JSP233.CoreFringe208
open StarCompletion APGeometry APCount41 CoreDensity208
open scoped Classical BigOperators
noncomputable section
set_option maxHeartbeats 0

theorem extra_points {S P Q : Finset ℤ} {a d delta phase qphase : ℤ} {p K : ℕ}
    (hP : APAt d phase P) (hQ : APAt delta qphase Q)
    (haP : a ∈ P) (haQ : a ∈ Q) (hend : a + (K : ℤ) * d ∈ Q)
    (hQS : Q ⊆ S) (hdiv : delta ∣ d) (hratio : (p : ℤ) * delta ≤ d) :
    K * (p - 1) ≤ (S \ P).card := by
  let f : ℕ × ℕ → ℤ := fun z => a + (z.1 : ℤ) * d + ((z.2 : ℤ) + 1) * delta
  let I := Finset.range K ×ˢ Finset.range (p - 1)
  have hbounds : ∀ z ∈ I, 0 < ((z.2 : ℤ) + 1) * delta ∧
      ((z.2 : ℤ) + 1) * delta < d := by
    intro z hz
    have hj := Finset.mem_range.mp (Finset.mem_product.mp hz).2
    have hjZ : (z.2 : ℤ) + 1 < p := by omega
    constructor
    · exact mul_pos (by omega) hQ.1
    · nlinarith only [hratio, hjZ, hQ.1]
  have hmaps : Set.MapsTo f (I : Set (ℕ × ℕ)) ((S \ P : Finset ℤ) : Set ℤ) := by
    intro z hz
    have hi := Finset.mem_range.mp (Finset.mem_product.mp hz).1
    obtain ⟨hpos, hlt⟩ := hbounds z hz
    have hyQ : f z ∈ Q := by
      apply apAt_fill hQ haQ hend
      · dsimp [f]
        have hm : 0 ≤ (z.1 : ℤ) * d := mul_nonneg (by positivity) hP.1.le
        linarith
      · dsimp [f]
        have hiZ : (z.1 : ℤ) + 1 ≤ K := by omega
        nlinarith only [hiZ, hP.1, hlt]
      · change delta ∣ a + (z.1 : ℤ) * d + ((z.2 : ℤ) + 1) * delta - a
        rw [show a + (z.1 : ℤ) * d + ((z.2 : ℤ) + 1) * delta - a =
          (z.1 : ℤ) * d + ((z.2 : ℤ) + 1) * delta by ring]
        exact dvd_add (dvd_mul_of_dvd_right hdiv _) (dvd_mul_left _ _)
    apply Finset.mem_sdiff.mpr
    refine ⟨hQS hyQ, ?_⟩
    intro hyP
    have hdv := apAt_dvd_sub hP haP hyP
    have he : f z - a = (z.1 : ℤ) * d + ((z.2 : ℤ) + 1) * delta := by dsimp [f]; ring
    rw [he] at hdv
    have hdv' := dvd_sub hdv (dvd_mul_left d (z.1 : ℤ))
    have hdv'' : d ∣ ((z.2 : ℤ) + 1) * delta := by simpa only [add_sub_cancel_left] using hdv'
    have hh := Int.le_of_dvd hpos hdv''
    omega
  have hinj : Set.InjOn f (I : Set (ℕ × ℕ)) := by
    intro z hz w hw he
    obtain ⟨hz0, hzd⟩ := hbounds z hz
    obtain ⟨hw0, hwd⟩ := hbounds w hw
    have hi : z.1 = w.1 := by
      by_contra hn
      rcases lt_or_gt_of_ne hn with hlt | hlt
      · have hh : (z.1 : ℤ) + 1 ≤ w.1 := by omega
        dsimp [f] at he
        nlinarith only [hh, hP.1, he, hzd, hw0]
      · have hh : (w.1 : ℤ) + 1 ≤ z.1 := by omega
        dsimp [f] at he
        nlinarith only [hh, hP.1, he, hwd, hz0]
    have hj : z.2 = w.2 := by
      dsimp [f] at he
      rw [hi] at he
      have hh : (z.2 : ℤ) = w.2 := by nlinarith only [he, hQ.1]
      exact_mod_cast hh
    exact Prod.ext hi hj
  have hc := Finset.card_le_card_of_injOn f hmaps hinj
  simpa only [I, Finset.card_product, Finset.card_range] using hc

theorem fringe_overlap_subset {S P Q : Finset ℤ} {a d phase : ℤ} {p K : ℕ}
    (hP : APAt d phase P) (hPS : P ⊆ S) (hQS : Q ⊆ S) (hQ : IsAP Q)
    (haP : a ∈ P) (haQ : a ∈ Q) (hadQ : a + d ∈ Q)
    (hend : a + (K : ℤ) * d ∈ Q)
    (hsmall : (S \ P).card < K * (p - 1))
    (hproper : ∀ delta : ℤ, 0 < delta → delta ∣ d → delta < d → (p : ℤ) * delta ≤ d)
    (hmax : ∀ R : Finset ℤ, IsAP R → R ⊆ S → R.card ≤ P.card) : Q ⊆ P := by
  obtain ⟨delta, q, hstep, _⟩ := (isAP_iff_exists_APAt Q).mp hQ
  have hdiv : delta ∣ d := by
    have hh := apAt_dvd_sub hstep haQ hadQ
    simpa only [add_sub_cancel_left] using hh
  have hle : delta ≤ d := Int.le_of_dvd hP.1 hdiv
  have heq : delta = d := by
    by_contra hne
    have hh := extra_points hP hstep haP haQ hend hQS hdiv
      (hproper delta hstep.1 hdiv (by omega))
    omega
  have hQd : APAt d a Q := by
    simpa only [heq] using apAt_rebase hstep haQ
  have hPd := apAt_rebase hP haP
  have hu : APAt d a (P ∪ Q) := by
    simpa only [APAt, Finset.mem_union] using
      PrivateUnion.union_APAt d a (fun x => x ∈ P) (fun x => x ∈ Q) hPd hQd haP haQ
  have hAPu : IsAP (P ∪ Q) := (isAP_iff_exists_APAt _).mpr
    ⟨d, a, hu, Finset.mem_union_left _ haP⟩
  have hc := hmax (P ∪ Q) hAPu (Finset.union_subset hPS hQS)
  have hunion : P ∪ Q = P := (Finset.eq_of_subset_of_card_le Finset.subset_union_left hc).symm
  rw [← hunion]
  exact Finset.subset_union_right

theorem unit_gate_overlap_subset {S P Q : Finset ℤ} {a d phase : ℤ} {p K A B E : ℕ}
    (hp : 2 ≤ p) (hB : B ≤ A) (hcard : A + 1 ≤ P.card) (hK : B + K = P.card)
    (hfee : (S \ P).card < E)
    (hgate : (p - 1) * (A + 1 - B) ≥ E ∨ p * B ≤ (p - 1) * (A + 1))
    (hP : APAt d phase P) (hPS : P ⊆ S) (hQS : Q ⊆ S) (hQ : IsAP Q)
    (haP : a ∈ P) (haQ : a ∈ Q) (hadQ : a + d ∈ Q)
    (hend : a + (K : ℤ) * d ∈ Q)
    (hproper : ∀ delta : ℤ, 0 < delta → delta ∣ d → delta < d → (p : ℤ) * delta ≤ d)
    (hmax : ∀ R : Finset ℤ, IsAP R → R ⊆ S → R.card ≤ P.card) : Q ⊆ P := by
  rcases hgate with hg | hg
  · apply fringe_overlap_subset hP hPS hQS hQ haP haQ hadQ hend _ hproper hmax
    have hlow : A + 1 - B ≤ K := by omega
    have hh := Nat.mul_le_mul_left (p - 1) hlow
    nlinarith only [hh, hg, hfee]
  · apply maximum_overlap_subset hP hPS hQS hQ haP haQ hadQ hend _ hproper hmax
    have hh := Nat.mul_le_mul_left (p - 1) hcard
    have hp' : p - 1 + 1 = p := by omega
    nlinarith only [hh, hg, hK, hp']

#print axioms extra_points
#print axioms fringe_overlap_subset
#print axioms unit_gate_overlap_subset
end
end JSP233.CoreFringe208
