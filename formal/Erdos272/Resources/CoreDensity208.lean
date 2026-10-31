import Erdos272.Counting.APCount41

/-! Maximum AP cardinality rules out a finer progression on a long overlap.
This is the density alternative in the unit core-block admissibility gate. -/
namespace JSP233.CoreDensity208
open StarCompletion APGeometry APCount41
open scoped Classical BigOperators
noncomputable section
set_option maxHeartbeats 0

theorem ap_card_from_density {Q : Finset ℤ} {a d delta phase : ℤ} {p K : ℕ}
    (hQ : APAt delta phase Q) (ha : a ∈ Q) (hb : a + (K : ℤ) * d ∈ Q)
    (hratio : (p : ℤ) * delta ≤ d) : p * K + 1 ≤ Q.card := by
  have hne : Q.Nonempty := ⟨a, ha⟩
  have hlow := (low_spec hne).2 a ha
  have hhigh := (high_spec hne).2 _ hb
  have hspan : High Q - Low Q = delta * ((Q.card : ℤ) - 1) := by
    simpa only [High, Low, dif_pos hne] using apAt_span_eq hQ hne
  have hm := mul_le_mul_of_nonneg_left hratio (show (0 : ℤ) ≤ K by positivity)
  have hc : delta * ((p : ℤ) * K) ≤ delta * ((Q.card : ℤ) - 1) := by
    nlinarith only [hlow, hhigh, hspan, hm]
  have hcard := (mul_le_mul_iff_right₀ hQ.1).mp hc
  exact_mod_cast (show (p : ℤ) * K + 1 ≤ Q.card by omega)

theorem maximum_overlap_subset {S P Q : Finset ℤ} {a d phase : ℤ} {p K : ℕ}
    (hP : APAt d phase P) (hPS : P ⊆ S) (hQS : Q ⊆ S) (hQ : IsAP Q)
    (haP : a ∈ P) (haQ : a ∈ Q) (hadQ : a + d ∈ Q)
    (hend : a + (K : ℤ) * d ∈ Q) (hsize : P.card ≤ p * K)
    (hproper : ∀ delta : ℤ, 0 < delta → delta ∣ d → delta < d → (p : ℤ) * delta ≤ d)
    (hmax : ∀ R : Finset ℤ, IsAP R → R ⊆ S → R.card ≤ P.card) : Q ⊆ P := by
  obtain ⟨delta, q, hstep, _⟩ := (isAP_iff_exists_APAt Q).mp hQ
  have hdiv : delta ∣ d := by
    have hh := apAt_dvd_sub hstep haQ hadQ
    simpa only [add_sub_cancel_left] using hh
  have hle : delta ≤ d := Int.le_of_dvd hP.1 hdiv
  have heq : delta = d := by
    by_contra hne
    have hh := ap_card_from_density hstep haQ hend (hproper delta hstep.1 hdiv (by omega))
    have hbound := hmax Q hQ hQS
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

theorem actual_remainder_private {N p K : ℕ} {F : Finset (Finset ℤ)}
    {S T P : Finset ℤ} {a d phase : ℤ}
    (hF : Legal (Ground N) F) (hS : S ∈ F) (hT : T ∈ F) (hne : S ≠ T)
    (hP : APAt d phase P) (hPS : P ⊆ S)
    (haP : a ∈ P) (hadP : a + d ∈ P) (hendP : a + (K : ℤ) * d ∈ P)
    (haT : a ∈ T) (hadT : a + d ∈ T) (hendT : a + (K : ℤ) * d ∈ T)
    (hsize : P.card ≤ p * K)
    (hproper : ∀ delta : ℤ, 0 < delta → delta ∣ d → delta < d → (p : ℤ) * delta ≤ d)
    (hmax : ∀ R : Finset ℤ, IsAP R → R ⊆ S → R.card ≤ P.card) : Disjoint (S \ P) T := by
  have hsub : S ∩ T ⊆ P := maximum_overlap_subset hP hPS Finset.inter_subset_left
    (hF.2 S hS T hT hne) haP (Finset.mem_inter.mpr ⟨hPS haP, haT⟩)
    (Finset.mem_inter.mpr ⟨hPS hadP, hadT⟩)
    (Finset.mem_inter.mpr ⟨hPS hendP, hendT⟩) hsize hproper hmax
  apply Finset.disjoint_left.mpr
  intro x hxS hxT
  obtain ⟨hxS, hxP⟩ := Finset.mem_sdiff.mp hxS
  exact hxP (hsub (Finset.mem_inter.mpr ⟨hxS, hxT⟩))

#print axioms ap_card_from_density
#print axioms maximum_overlap_subset
#print axioms actual_remainder_private
end
end JSP233.CoreDensity208
