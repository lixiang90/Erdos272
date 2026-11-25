module

public import Erdos272.Geometry.N88404.PhaseCard88404
public import Erdos272.Capacity.N88404.SieveBound88404
public import Erdos272.Capacity.N88404.SieveConstants88404
public import Erdos272.Counting.N88404.APClassFrame88404

@[expose] public section

namespace JSP233.SievePieces88404
open StarCompletion APGeometry APShadowCapacity16858 AffineLine30 AffineShadow94488
open OrderedShadow88404 PhaseCard88404 InclusionExclusion88404 SieveConstants88404
open APClasses88404 APClassFrame88404
open scoped Classical BigOperators
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2000000

theorem reciprocal_product (J : Finset ℕ) (k : ℕ) :
    (∏ j ∈ J, (1 : ℝ)/(j : ℝ)^k) = 1/((∏ j ∈ J, j : ℕ) : ℝ)^k := by
  induction J using Finset.induction_on with
  | empty => simp
  | @insert a J ha ih =>
      rw [Finset.prod_insert ha, Finset.prod_insert ha, ih, Nat.cast_mul, mul_pow]
      simp only [one_div, mul_inv_rev]
      ring

theorem frame_piece_bound {N d : ℕ} {U : Finset (Finset ℤ)}
    (hdS : d ∈ Steps) (f : Frame N d U) (r : ℕ → ℤ) :
    Alpha d*((APShadow U).card : ℝ)-Error d*(f.size : ℝ)^2 ≤
      (Avoid (APShadow U) (fun j => AllPhase j (r j)) (Later d)).card := by
  have hd := steps_positive hdS
  have hdZ : (0 : ℤ) < d := by exact_mod_cast hd
  let T := APShadow f.family
  have hT : T ⊆ (Ground f.size).powersetCard 3 := shadow_carrier f.ground
  have hclosed : Closed T := shadow_closed f.intervals
  have he : APShadow U = T.image (mapSet f.offset (d : ℤ)) := by
    exact (congrArg APShadow f.mapped).symm.trans (map_shadow f.offset (d : ℤ) hdZ f.family)
  have hcard : (APShadow U).card = T.card := by
    rw [he]
    exact Finset.card_image_of_injective _ (mapSet_injective f.offset (d : ℤ) hdZ)
  have hbounds : ∀ K ⊆ Later d, K.Nonempty →
      ((APShadow U).card : ℝ)*(∏ j ∈ K, (1 : ℝ)/(j : ℝ)^3)-
          (3/2 : ℝ)*(f.size : ℝ)^2*(∏ j ∈ K, (1 : ℝ)/(j : ℝ)^2) ≤
        (Intersect (APShadow U) (fun j => AllPhase j (r j)) K).card ∧
      ((Intersect (APShadow U) (fun j => AllPhase j (r j)) K).card : ℝ) ≤
        ((APShadow U).card : ℝ)*(∏ j ∈ K, (1 : ℝ)/(j : ℝ)^3)+
          (1/2 : ℝ)*(f.size : ℝ)^2*(∏ j ∈ K, (1 : ℝ)/(j : ℝ)^2) := by
    intro K hK hne
    have hKS : K ⊆ Steps := by
      intro j hj
      exact Finset.mem_insert_of_mem (Finset.mem_filter.mp (hK hj)).1
    have hpos : ∀ j ∈ K, 0 < j := fun j hj => steps_positive (hKS hj)
    have hpair : Set.Pairwise (↑K) Nat.Coprime := by
      intro i hi j hj hij
      exact steps_pairwise_coprime (hKS hi) (hKS hj) hij
    have hcop : ∀ j ∈ K, Nat.Coprime d j := by
      intro j hj
      exact steps_pairwise_coprime hdS (hKS hj) (ne_of_lt (Finset.mem_filter.mp (hK hj)).2)
    have hh := affine_intersection_density hT hclosed hd K id hpos hpair hcop f.offset r
    dsimp only [id_eq] at hh
    rw [← he] at hh
    rw [hcard, reciprocal_product K 3, reciprocal_product K 2]
    dsimp only [Intersect]
    have hlo := hh.1
    have hhi := hh.2
    ring_nf at hlo hhi ⊢
    exact ⟨hlo, hhi⟩
  have hh := SieveBound88404.sieve_lower (APShadow U) (fun j => AllPhase j (r j))
    (Later d) (fun j => (1 : ℝ)/(j : ℝ)^2) (fun j => (1 : ℝ)/(j : ℝ)^3)
    ((f.size : ℝ)^2) (fun j _ => by positivity) hbounds
  simpa only [Alpha, Error, mul_comm] using hh

theorem frame_shadow_phase {N d : ℕ} {U : Finset (Finset ℤ)}
    (hd : 0 < d) (f : Frame N d U) {Q : Finset ℤ} (hQ : Q ∈ APShadow U) :
    AllPhase d f.offset Q := by
  have hdZ : (0 : ℤ) < d := by exact_mod_cast hd
  rw [← f.mapped, map_shadow f.offset (d : ℤ) hdZ] at hQ
  obtain ⟨V, hV, rfl⟩ := Finset.mem_image.mp hQ
  apply all_phase_affine.mpr
  intro x hx
  have he : f.offset+(d : ℤ)*x-f.offset = (d : ℤ)*x := by ring
  rw [he]
  exact dvd_mul_right _ _

theorem pieces_disjoint (S : ℕ → Finset (Finset ℤ)) (r : ℕ → ℤ)
    (hphase : ∀ p ∈ Steps, ∀ Q ∈ S p, AllPhase p (r p) Q) :
    Set.Pairwise (↑Steps) (fun p q => Disjoint
      (Avoid (S p) (fun j => AllPhase j (r j)) (Later p))
      (Avoid (S q) (fun j => AllPhase j (r j)) (Later q))) := by
  intro p hp q hq hpq
  apply Finset.disjoint_left.mpr
  intro Q hP hQ
  obtain ⟨hP, hpavoid⟩ := Finset.mem_filter.mp hP
  obtain ⟨hQ, hqavoid⟩ := Finset.mem_filter.mp hQ
  have hlater : ∀ a b : ℕ, a ∈ Steps → b ∈ Steps → a < b → b ∈ Later a := by
    intro a b ha hb hab
    have hbS : b ∈ Selected := by
      have hh := Finset.mem_insert.mp hb
      rcases hh with hh | hh
      · have ha0 := steps_positive ha
        omega
      · exact hh
    exact Finset.mem_filter.mpr ⟨hbS, hab⟩
  rcases lt_or_gt_of_ne hpq with hlt | hgt
  · exact hpavoid q (hlater p q hp hq hlt) (hphase q hq Q hQ)
  · exact hqavoid p (hlater q p hq hp hgt) (hphase p hp Q hP)

#print axioms reciprocal_product
#print axioms frame_piece_bound
#print axioms frame_shadow_phase
#print axioms pieces_disjoint
end
end JSP233.SievePieces88404
