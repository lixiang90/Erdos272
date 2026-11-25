module

public import Erdos272.Geometry.N20258.OffGridPool20258

@[expose] public section
namespace JSP233.ExteriorFarPool20258
open StarCompletion APGeometry PairPool200000 IntrinsicTriples208
open scoped Classical
noncomputable section
set_option autoImplicit false

/-- If the gap to the exterior point exceeds the whole core width, any
pair of distinct core points gives an intrinsic triple with that point. -/
theorem actual {P : Finset ℤ} {x a b : ℤ} (bounds : P⊆Finset.Icc a b)
    (outside : b-a<a-x ∨ b-a<x-b) (out : x∉P) :
    P.card.choose 2≤(Pool (insert x P)).card := by
  let S := insert x P
  have good : P.powersetCard 2⊆GoodPairs S P x := by
    intro Q hQ
    obtain ⟨sub,two⟩ := Finset.mem_powersetCard.mp hQ
    have xQ : x∉Q := fun hx => out (sub hx)
    unfold GoodPairs
    refine Finset.mem_filter.mpr ⟨hQ,?_⟩
    apply mem_pool.mpr
    refine ⟨Finset.insert_subset_insert _ sub,by rw [Finset.card_insert_of_notMem xQ,two],?_⟩
    rintro ⟨T,hT,cover,inside⟩
    obtain ⟨u,v,neq,eqn⟩ := Finset.card_eq_two.mp two
    have hu : u∈Q := by rw [eqn]; simp
    have hv : v∈Q := by rw [eqn]; simp
    have ub := Finset.mem_Icc.mp (bounds (sub hu))
    have vb := Finset.mem_Icc.mp (bounds (sub hv))
    have uT := cover (Finset.mem_insert_of_mem hu)
    have vT := cover (Finset.mem_insert_of_mem hv)
    have xT := cover (Finset.mem_insert_self _ _)
    obtain ⟨e,q,frame,_⟩ := (isAP_iff_exists_APAt T).mp hT
    have pos := frame.1
    have small : e≤b-a := by
      rcases lt_or_gt_of_ne neq with h|h
      · have := Int.le_of_dvd (by omega : 0<v-u) (apAt_dvd_sub frame uT vT)
        omega
      · have := Int.le_of_dvd (by omega : 0<u-v) (apAt_dvd_sub frame vT uT)
        omega
    rcases outside with left | right
    · have near : x+e∈T := apAt_fill frame xT uT (by omega) (by omega) (by simp)
      have p := (Finset.mem_insert.mp (inside near)).resolve_left (by omega)
      have := Finset.mem_Icc.mp (bounds p)
      omega
    · have div : e∣x-e-u := by
        rw [show x-e-u=(x-u)-e by ring]
        exact dvd_sub (apAt_dvd_sub frame uT xT) (dvd_refl e)
      have near : x-e∈T := apAt_fill frame uT xT (by omega) (by omega) div
      have p := (Finset.mem_insert.mp (inside near)).resolve_left (by omega)
      have := Finset.mem_Icc.mp (bounds p)
      omega
  have bound := Finset.card_le_card good
  rw [Finset.card_powersetCard] at bound
  have has : x∈S\P := Finset.mem_sdiff.mpr ⟨Finset.mem_insert_self _ _,out⟩
  have inc : PointTriples S P x⊆Pool S :=
    (Finset.subset_biUnion_of_mem (PointTriples S P) has).trans (point_union_subset S P)
  rw [← point_triples_card (S:=S) out] at bound
  exact bound.trans (Finset.card_le_card inc)

#print axioms actual
end
end JSP233.ExteriorFarPool20258
