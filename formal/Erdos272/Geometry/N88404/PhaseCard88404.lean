module

public import Erdos272.Counting.N88404.ResidueDensity88404
public import Erdos272.Geometry.N88404.AffineCRT88404
public import Erdos272.Geometry.N94488.AffineShadow94488

@[expose] public section

namespace JSP233.PhaseCard88404
open StarCompletion APGeometry AffineLine30 AffineShadow94488
open OrderedShadow88404 ResidueMaps88404 ResidueDensity88404
open scoped Classical BigOperators
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2000000

def AllPhase (q : ℕ) (r : ℤ) (Q : Finset ℤ) : Prop :=
  ∀ x ∈ Q, Phase q r x

theorem all_phase_triple {q : ℕ} {r : ℤ} {p : PointTriple} :
    AllPhase q r (Triple p) ↔ PhaseTriple q r p := by
  simp [AllPhase, Triple, PhaseTriple]

theorem all_phase_affine {q : ℕ} {r c d : ℤ} {Q : Finset ℤ} :
    AllPhase q r (mapSet c d Q) ↔ ∀ x ∈ Q, (q : ℤ) ∣ c+d*x-r := by
  simp [AllPhase, mapSet, affine, Phase]

theorem affine_codes_image {M : ℕ} {T : Finset (Finset ℤ)}
    (hT : T ⊆ (Ground M).powersetCard 3) (c d : ℤ) :
    (Codes M T).image (fun p => mapSet c d (Triple p)) = T.image (mapSet c d) := by
  calc
    _ = ((Codes M T).image Triple).image (mapSet c d) :=
      (Finset.image_image (s := Codes M T) (f := Triple) (g := mapSet c d)).symm
    _ = _ := by rw [codes_image hT]

theorem affine_codes_injective {M : ℕ} {T : Finset (Finset ℤ)} {c d : ℤ}
    (hd : 0 < d) : Set.InjOn (fun p => mapSet c d (Triple p)) (Codes M T) := by
  intro p hp s hs he
  apply triple_injective (mem_codes.mp hp).2.2.2.1 (mem_codes.mp hs).2.2.2.1
  exact mapSet_injective c d hd he

theorem affine_intersection_card {ι : Type*} [DecidableEq ι]
    {M d : ℕ} {T : Finset (Finset ℤ)} (hT : T ⊆ (Ground M).powersetCard 3)
    (hd : 0 < d) (J : Finset ι) (m : ι → ℕ) (c : ℤ) (r : ι → ℤ)
    (b : ℤ) (hb : ∀ x : ℤ, (∀ j ∈ J, (m j : ℤ) ∣ c+(d : ℤ)*x-r j) ↔
      ((∏ j ∈ J, m j : ℕ) : ℤ) ∣ x-b) :
    (((T.image (mapSet c (d : ℤ))).filter
      (fun Q => ∀ j ∈ J, AllPhase (m j) (r j) Q)).card) =
      (ResidueCodes M (∏ j ∈ J, m j) b T).card := by
  have hdZ : (0 : ℤ) < d := by exact_mod_cast hd
  rw [← affine_codes_image hT c (d : ℤ)]
  symm
  apply Finset.card_bij (fun p _ => mapSet c (d : ℤ) (Triple p))
  · intro p hp
    obtain ⟨hp, hphase⟩ := mem_residue.mp hp
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_image.mpr ⟨p, hp, rfl⟩, ?_⟩
    intro j hj
    apply all_phase_affine.mpr
    intro x hx
    exact (hb x).mpr ((all_phase_triple.mpr hphase) x hx) j hj
  · intro p hp s hs he
    exact affine_codes_injective (c := c) hdZ (mem_residue.mp hp).1 (mem_residue.mp hs).1 he
  · intro Q hQ
    obtain ⟨hQ, hphase⟩ := Finset.mem_filter.mp hQ
    obtain ⟨p, hp, rfl⟩ := Finset.mem_image.mp hQ
    refine ⟨p, mem_residue.mpr ⟨hp, ?_⟩, rfl⟩
    apply all_phase_triple.mp
    intro x hx
    apply (hb x).mp
    intro j hj
    exact (all_phase_affine.mp (hphase j hj)) x hx

theorem affine_intersection_density {ι : Type*} [DecidableEq ι]
    {M d : ℕ} {T : Finset (Finset ℤ)}
    (hT : T ⊆ (Ground M).powersetCard 3) (hclosed : Closed T) (hd : 0 < d)
    (J : Finset ι) (m : ι → ℕ) (hpos : ∀ j ∈ J, 0 < m j)
    (hpair : Set.Pairwise (↑J) (fun i j => Nat.Coprime (m i) (m j)))
    (hdcop : ∀ j ∈ J, Nat.Coprime d (m j)) (c : ℤ) (r : ι → ℤ) :
    let q := ∏ j ∈ J, m j
    let I := (T.image (mapSet c (d : ℤ))).filter (fun Q => ∀ j ∈ J, AllPhase (m j) (r j) Q)
    (T.card : ℝ)/(q : ℝ)^3-3*(M : ℝ)^2/(2*(q : ℝ)^2) ≤ I.card ∧
      (I.card : ℝ) ≤ (T.card : ℝ)/(q : ℝ)^3+(M : ℝ)^2/(2*(q : ℝ)^2) := by
  obtain ⟨b, hb⟩ := AffineCRT88404.affine_crt J m hpos hpair d hd hdcop c r
  have hq : 0 < ∏ j ∈ J, m j := Finset.prod_pos hpos
  have hc := affine_intersection_card hT hd J m c r b hb
  dsimp only
  rw [hc]
  exact residue_density hq hT hclosed

#print axioms all_phase_triple
#print axioms all_phase_affine
#print axioms affine_codes_image
#print axioms affine_codes_injective
#print axioms affine_intersection_card
#print axioms affine_intersection_density
end
end JSP233.PhaseCard88404
