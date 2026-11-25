module

public import Erdos272.Counting.N86412.APSegments86412
public import Erdos272.Counting.N86412.OrderedFinite86412

@[expose] public section

namespace JSP233.GapShape86412
open ActualAPCount208 APSegments86412 OrderedFinite86412 APReflection86412
open scoped Classical
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1500000

def NoBetween (S : Finset ℤ) (x y : ℤ) : Prop :=
  ∀ z ∈ S, x < z → z < y → False

def Edge (S : Finset ℤ) (x y : ℤ) : Prop :=
  (∀ z ∈ S, x ≤ z) ∨ (∀ z ∈ S, z ≤ y)

def GapShape (S : Finset ℤ) (d : ℤ) : Prop :=
  ∀ x ∈ S, ∀ y ∈ S, x < y → NoBetween S x y →
    y-x=d ∨ (y-x=2*d ∧ Edge S x y)

def LeftGapShape (S : Finset ℤ) (d : ℤ) : Prop :=
  ∀ x ∈ S, ∀ y ∈ S, x < y → NoBetween S x y →
    y-x=d ∨ (y-x=2*d ∧ ∀ z ∈ S, x ≤ z)

def RightGapShape (S : Finset ℤ) (d : ℤ) : Prop :=
  ∀ x ∈ S, ∀ y ∈ S, x < y → NoBetween S x y →
    y-x=d ∨ (y-x=2*d ∧ ∀ z ∈ S, z ≤ y)

theorem restrict_no_between {S T : Finset ℤ} {x y : ℤ}
    (hTS : T ⊆ S) (hgap : NoBetween S x y) : NoBetween T x y := by
  intro z hz
  exact hgap z (hTS hz)

theorem initial_no_between {S T : Finset ℤ} {x y : ℤ}
    (hT : IsInitial S T) (hy : y ∈ T) (hgap : NoBetween T x y) :
    NoBetween S x y := by
  intro z hz hxz hzy
  exact hgap z (hT.2 z hz y hy hzy.le) hxz hzy

theorem complement_no_between {S A : Finset ℤ} {x y : ℤ}
    (hA : IsInitial S A) (hx : x ∈ S\A) (hgap : NoBetween (S\A) x y) :
    NoBetween S x y := by
  intro z hz hxz hzy
  have hzA : z ∉ A := by
    intro ha
    exact (Finset.mem_sdiff.mp hx).2 (hA.2 x (Finset.mem_sdiff.mp hx).1 z ha hxz.le)
  exact hgap z (Finset.mem_sdiff.mpr ⟨hz, hzA⟩) hxz hzy

theorem initial_min {S T : Finset ℤ} {x : ℤ}
    (hT : IsInitial S T) (hx : x ∈ T) (hmin : ∀ z ∈ T, x ≤ z) :
    ∀ z ∈ S, x ≤ z := by
  intro z hz
  by_contra hh
  have hzT := hT.2 z hz x hx (by omega)
  have hh' := hmin z hzT
  omega

theorem complement_max {S A : Finset ℤ} {y : ℤ}
    (hA : IsInitial S A) (hy : y ∈ S\A) (hmax : ∀ z ∈ S\A, z ≤ y) :
    ∀ z ∈ S, z ≤ y := by
  intro z hz
  by_cases hzA : z ∈ A
  · exact (initial_before hA hzA hy).le
  · exact hmax z (Finset.mem_sdiff.mpr ⟨hz, hzA⟩)

theorem adjacent_pair_cover {S T A : Finset ℤ} {x y : ℤ}
    (hT : IsInitial S T) (hA : IsInitial T A) (hmiddle : (T\A).Nonempty)
    (hx : x ∈ S) (hy : y ∈ S) (hxy : x < y) (hgap : NoBetween S x y) :
    (x ∈ T ∧ y ∈ T) ∨ (x ∈ S\A ∧ y ∈ S\A) := by
  by_cases hyT : y ∈ T
  · exact Or.inl ⟨hT.2 x hx y hyT hxy.le, hyT⟩
  · have hyA : y ∉ A := fun hh => hyT (hA.1 hh)
    have hxA : x ∉ A := by
      intro hh
      obtain ⟨u, hu⟩ := hmiddle
      have hxu := initial_before hA hh hu
      have huy := initial_before hT (Finset.mem_sdiff.mp hu).1
        (Finset.mem_sdiff.mpr ⟨hy, hyT⟩)
      exact hgap u (hT.1 (Finset.mem_sdiff.mp hu).1) hxu huy
    exact Or.inr ⟨Finset.mem_sdiff.mpr ⟨hx, hxA⟩, Finset.mem_sdiff.mpr ⟨hy, hyA⟩⟩

theorem one_sided_glue {S T A : Finset ℤ} {d : ℤ}
    (hT : IsInitial S T) (hA : IsInitial T A) (hmiddle : (T\A).Nonempty)
    (hleft : LeftGapShape T d) (hright : RightGapShape (S\A) d) :
    GapShape S d := by
  intro x hx y hy hxy hgap
  rcases adjacent_pair_cover hT hA hmiddle hx hy hxy hgap with hpair | hpair
  · rcases hleft x hpair.1 y hpair.2 hxy (restrict_no_between hT.1 hgap) with hh | hh
    · exact Or.inl hh
    · exact Or.inr ⟨hh.1, Or.inl (initial_min hT hpair.1 hh.2)⟩
  · rcases hright x hpair.1 y hpair.2 hxy
        (restrict_no_between Finset.sdiff_subset hgap) with hh | hh
    · exact Or.inl hh
    · exact Or.inr ⟨hh.1, Or.inr (complement_max (initial_trans hT hA) hpair.2 hh.2)⟩

theorem left_reflection {S : Finset ℤ} {d : ℤ}
    (hleft : LeftGapShape (NegSet S) d) : RightGapShape S d := by
  intro x hx y hy hxy hgap
  have hxN : -x ∈ NegSet S := mem_negset.mpr (by simpa only [neg_neg] using hx)
  have hyN : -y ∈ NegSet S := mem_negset.mpr (by simpa only [neg_neg] using hy)
  have hno : NoBetween (NegSet S) (-y) (-x) := by
    intro z hz hyz hzx
    exact hgap (-z) (mem_negset.mp hz) (by omega) (by omega)
  rcases hleft (-y) hyN (-x) hxN (by omega) hno with hh | ⟨hh, hmin⟩
  · exact Or.inl (by omega)
  · refine Or.inr ⟨by omega, ?_⟩
    intro z hz
    have hh' := hmin (-z) (mem_negset.mpr (by simpa only [neg_neg] using hz))
    omega

theorem glue {S T A : Finset ℤ} {d₁ d₂ : ℤ}
    (hT : IsInitial S T) (hA : IsInitial T A)
    (hane : A.Nonempty) (hbne : (S\T).Nonempty) (hmiddle : 3 ≤ (T\A).card)
    (hfirst : GapShape T d₁) (hsecond : GapShape (S\A) d₂)
    (hd₁ : 0 < d₁) (hd₂ : 0 < d₂) :
    d₁ = d₂ ∧ GapShape S d₁ := by
  let M := T\A
  let u := point M 0
  let v := point M 1
  let w := point M 2
  have hu : u ∈ T\A := FarShort112.point_mem (by change 0 < (T\A).card; omega)
  have hv : v ∈ T\A := FarShort112.point_mem (by change 1 < (T\A).card; omega)
  have hw : w ∈ T\A := FarShort112.point_mem (by change 2 < (T\A).card; omega)
  have huv : u < v := FarShort112.point_strict (by decide : 0 < 1)
    (by change 1 < (T\A).card; omega)
  have hvw : v < w := FarShort112.point_strict (by decide : 1 < 2)
    (by change 2 < (T\A).card; omega)
  have hsub : T\A ⊆ S\A := (difference_initial hT hA).1
  have huU := hsub hu
  have hvU := hsub hv
  have hwU := hsub hw
  have hnoUV : NoBetween (T\A) u v :=
    consecutive_no_between (by change 1 < (T\A).card; omega)
  have hnoVW : NoBetween (T\A) v w :=
    consecutive_no_between (by change 2 < (T\A).card; omega)
  have hnoUVT := complement_no_between hA hu hnoUV
  have hnoVWT := complement_no_between hA hv hnoVW
  have hnoUVU := initial_no_between (difference_initial hT hA) hv hnoUV
  have hnoVWU := initial_no_between (difference_initial hT hA) hw hnoVW
  obtain ⟨a, ha⟩ := hane
  obtain ⟨b, hb⟩ := hbne
  have hau := initial_before hA ha hu
  have hwb := initial_before hT (Finset.mem_sdiff.mp hw).1 hb
  have hbU : b ∈ S\A := Finset.mem_sdiff.mpr ⟨(Finset.mem_sdiff.mp hb).1,
    fun hh => (Finset.mem_sdiff.mp hb).2 (hA.1 hh)⟩
  have hUV : v-u=d₁ := by
    rcases hfirst u (Finset.mem_sdiff.mp hu).1 v (Finset.mem_sdiff.mp hv).1 huv hnoUVT
      with hh | ⟨hh, hedge⟩
    · exact hh
    · rcases hedge with hedge | hedge
      · have hh' := hedge a (hA.1 ha); omega
      · have hh' := hedge w (Finset.mem_sdiff.mp hw).1; omega
  have hVW : w-v=d₂ := by
    rcases hsecond v hvU w hwU hvw hnoVWU with hh | ⟨hh, hedge⟩
    · exact hh
    · rcases hedge with hedge | hedge
      · have hh' := hedge u huU; omega
      · have hh' := hedge b hbU; omega
  have heq : d₁=d₂ := by
    have hUV' := hsecond u huU v hvU huv hnoUVU
    have hVW' := hfirst v (Finset.mem_sdiff.mp hv).1 w (Finset.mem_sdiff.mp hw).1 hvw hnoVWT
    rcases hUV' with hh | ⟨hh, _⟩ <;> rcases hVW' with hh' | ⟨hh', _⟩ <;> omega
  refine ⟨heq, ?_⟩
  intro x hx y hy hxy hgap
  rcases adjacent_pair_cover hT hA ⟨u, hu⟩ hx hy hxy hgap with hpair | hpair
  · rcases hfirst x hpair.1 y hpair.2 hxy (restrict_no_between hT.1 hgap)
      with hh | ⟨hh, hedge⟩
    · exact Or.inl hh
    · rcases hedge with hmin | hmax
      · exact Or.inr ⟨hh, Or.inl (initial_min hT hpair.1 hmin)⟩
      · have hwy := hmax w (Finset.mem_sdiff.mp hw).1
        have hvy : v < y := lt_of_lt_of_le hvw hwy
        have hvx : v ≤ x := by
          by_contra hlt
          exact hgap v (hT.1 (Finset.mem_sdiff.mp hv).1) (by omega) hvy
        have hux : u < x := lt_of_lt_of_le huv hvx
        have hxA : x ∉ A := by
          intro hxa
          exact (Finset.mem_sdiff.mp hu).2 (hA.2 u (Finset.mem_sdiff.mp hu).1 x hxa hux.le)
        have hyA : y ∉ A := by
          intro hya
          exact hxA (hA.2 x hpair.1 y hya hxy.le)
        have hxU := Finset.mem_sdiff.mpr ⟨hx, hxA⟩
        have hyU := Finset.mem_sdiff.mpr ⟨hy, hyA⟩
        have hyb := initial_before hT hpair.2 hb
        rcases hsecond x hxU y hyU hxy
            (restrict_no_between Finset.sdiff_subset hgap) with hh' | ⟨hh', hedge'⟩
        · omega
        · rcases hedge' with hmin' | hmax'
          · have hxu := hmin' u huU; omega
          · have hby := hmax' b hbU; omega
  · have hpairU := hpair
    rcases hsecond x hpair.1 y hpair.2 hxy
        (restrict_no_between Finset.sdiff_subset hgap) with hh | ⟨hh, hedge⟩
    · exact Or.inl (hh.trans heq.symm)
    · have hstep : y-x=2*d₁ := by omega
      rcases hedge with hmin | hmax
      · by_cases hyT : y ∈ T
        · have hxT := hT.2 x hx y hyT hxy.le
          have hav := initial_before (initial_trans hT hA) ha hpairU.1
          have hxu := hmin u huU
          have hxv : x < v := lt_of_le_of_lt hxu huv
          have hyv : y ≤ v := by
            by_contra hlt
            exact hgap v (hT.1 (Finset.mem_sdiff.mp hv).1) hxv (by omega)
          have hyw : y < w := lt_of_le_of_lt hyv hvw
          rcases hfirst x hxT y hyT hxy (restrict_no_between hT.1 hgap)
              with hh' | ⟨hh', hedge'⟩
          · omega
          · rcases hedge' with hmin' | hmax'
            · have hxa := hmin' a (hA.1 ha); omega
            · have hwy := hmax' w (Finset.mem_sdiff.mp hw).1; omega
        · have hxu := hmin u huU
          have hxv : x < v := lt_of_le_of_lt hxu huv
          have hvy := initial_before hT (Finset.mem_sdiff.mp hv).1
            (Finset.mem_sdiff.mpr ⟨hy, hyT⟩)
          exact (hgap v (hT.1 (Finset.mem_sdiff.mp hv).1) hxv hvy).elim
      · exact Or.inr ⟨hstep, Or.inr (complement_max (initial_trans hT hA) hpairU.2 hmax)⟩

#print axioms restrict_no_between
#print axioms initial_no_between
#print axioms complement_no_between
#print axioms initial_min
#print axioms complement_max
#print axioms adjacent_pair_cover
#print axioms one_sided_glue
#print axioms left_reflection
#print axioms glue
end
end JSP233.GapShape86412
