module

public import Erdos272.Geometry.N94488.AffineShadow94488

@[expose] public section

namespace JSP233.AffineIndex88404
open StarCompletion APGeometry AffineLine30 OneThird32 AffineShadow94488
open scoped Classical
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1500000

def Index (p d : ℤ) (S : Finset ℤ) : Finset ℤ :=
  (S.filter (fun x => d ∣ x-p)).image (fun x => (x-p)/d)

theorem mem_index {p d x : ℤ} {S : Finset ℤ} (hd : 0 < d) :
    x ∈ Index p d S ↔ p+d*x ∈ S := by
  constructor
  · intro hx
    obtain ⟨y, hy, he⟩ := Finset.mem_image.mp hx
    obtain ⟨hyS, hydiv⟩ := Finset.mem_filter.mp hy
    have hm := Int.ediv_mul_cancel hydiv
    rw [he] at hm
    have hh : p+d*x = y := by nlinarith only [hm]
    simpa only [hh] using hyS
  · intro hx
    have hdiv : d ∣ p+d*x-p := ⟨x, by ring⟩
    refine Finset.mem_image.mpr ⟨p+d*x, Finset.mem_filter.mpr ⟨hx, hdiv⟩, ?_⟩
    apply affine_injective p d hd
    have hm := Int.ediv_mul_cancel hdiv
    dsimp only [affine]
    nlinarith only [hm]

theorem map_index {p d : ℤ} (hd : 0 < d) (S : Finset ℤ) :
    mapSet p d (Index p d S) = S.filter (fun x => d ∣ x-p) := by
  ext y
  constructor
  · intro hy
    obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp hy
    have hm := (mem_index hd).mp hx
    exact Finset.mem_filter.mpr ⟨hm, ⟨x, by dsimp only [affine]; ring⟩⟩
  · intro hy
    obtain ⟨hyS, hydiv⟩ := Finset.mem_filter.mp hy
    have hm := Int.ediv_mul_cancel hydiv
    have he : affine p d ((y-p)/d) = y := by dsimp only [affine]; nlinarith only [hm]
    have hmem : (y-p)/d ∈ Index p d S := by
      apply (mem_index hd).mpr
      change affine p d ((y-p)/d) ∈ S
      rw [he]
      exact hyS
    exact Finset.mem_image.mpr ⟨(y-p)/d, hmem, he⟩

theorem map_index_of_phase {p d : ℤ} {S : Finset ℤ} (hd : 0 < d)
    (hphase : ∀ x ∈ S, d ∣ x-p) : mapSet p d (Index p d S) = S := by
  rw [map_index hd]
  exact Finset.filter_eq_self.mpr hphase

theorem index_family {p d : ℤ} {U : Finset (Finset ℤ)} (hd : 0 < d)
    (hphase : ∀ S ∈ U, ∀ x ∈ S, d ∣ x-p) :
    mapFamily p d (U.image (Index p d)) = U := by
  ext S
  constructor
  · intro hS
    obtain ⟨T, hT, rfl⟩ := Finset.mem_image.mp hS
    obtain ⟨V, hV, rfl⟩ := Finset.mem_image.mp hT
    simpa only [map_index_of_phase hd (hphase V hV)] using hV
  · intro hS
    exact Finset.mem_image.mpr ⟨Index p d S, Finset.mem_image.mpr ⟨S, hS, rfl⟩,
      map_index_of_phase hd (hphase S hS)⟩

theorem index_interval {p d q : ℤ} {S : Finset ℤ} (hd : 0 < d)
    (hS : APAt d q S) : OneThird32.Interval (Index p d S) := by
  intro a ha b hb x hax hxb
  have hA := (mem_index hd).mp ha
  have hB := (mem_index hd).mp hb
  apply (mem_index hd).mpr
  exact apAt_fill hS hA hB
    ((affine_strictMono p d hd).monotone hax)
    ((affine_strictMono p d hd).monotone hxb) ⟨x-a, by ring⟩

#print axioms mem_index
#print axioms map_index
#print axioms map_index_of_phase
#print axioms index_family
#print axioms index_interval
end
end JSP233.AffineIndex88404
