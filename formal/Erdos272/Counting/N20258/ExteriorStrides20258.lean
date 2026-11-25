module

public import Erdos272.Counting.N20258.ExteriorPrefix20258
public import Erdos272.Geometry.Reflect37
public import Erdos272.Foundation.JSP233

@[expose] public section
namespace JSP233.ExteriorStrides20258
open StarCompletion AffineLine30 ExteriorPrefix20258 Reflect37
open scoped Classical BigOperators
noncomputable section
set_option autoImplicit false

private theorem signed_pull {r d : ℤ} (hd : d≠0) {S : Finset ℤ}
    (h : IsAP (mapSet r d S)) : IsAP S := by
  by_cases pos : 0<d
  · exact (affine_isAP_iff r d pos S).mp h
  · have eqn : mapSet r (-d) (Reflect S)=mapSet r d S := by
      unfold mapSet Reflect
      rw [Finset.image_image]
      apply Finset.image_congr
      intro z _
      dsimp [Function.comp,affine]
      ring
    rw [← eqn] at h
    exact (reflect_isAP_iff S).mp ((affine_isAP_iff r (-d) (by omega) _).mp h)

private theorem rebase (r d k m t : ℤ) :
    mapSet (r+d*k) d (shape m 0 t)=mapSet r d (shape m k t) := by
  have shift (z : ℤ) : z∈shape m k t ↔ z-k∈shape m 0 t := by
    simp only [shape,Finset.mem_insert,Finset.mem_Icc]
    omega
  ext x
  constructor
  · rintro hx
    obtain ⟨z,hz,rfl⟩ := Finset.mem_image.mp hx
    have inside : k+z∈shape m k t := (shift _).mpr (by simpa using hz)
    exact Finset.mem_image.mpr ⟨k+z,inside,by dsimp [affine]; ring⟩
  · rintro hx
    obtain ⟨z,hz,rfl⟩ := Finset.mem_image.mp hx
    exact Finset.mem_image.mpr ⟨z-k,(shift _).mp hz,by dsimp [affine]; ring⟩

/-- All members represented with the same signed step meet one residue class.
The core starts and the exterior distances may be chosen separately for each member. -/
theorem fixed_step {Ω : Finset ℤ} {G : Finset (Finset ℤ)} {m T : ℕ} {d : ℤ}
    (legal : Legal Ω G) (hd : d≠0) (top : T≤m)
    (repr : ∀ S∈G, ∃ a t : ℤ, 2≤t ∧ t≤T ∧ S=mapSet a d (shape m 0 t)) :
    G.card≤oneSide m T := by
  classical
  by_cases ne : G.Nonempty
  · obtain ⟨A,hA⟩ := ne
    obtain ⟨r,u,_,_,ref⟩ := repr A hA
    have relative (S : Finset ℤ) : ∃ k t : ℤ, S∈G →
        2≤t ∧ t≤T ∧ S=mapSet r d (shape m k t) := by
      by_cases hs : S∈G
      · obtain ⟨a,t,low,high,eqn⟩ := repr S hs
        have meet : (A∩S).Nonempty := by
          by_cases same : A=S
          · rw [← same,Finset.inter_self]
            have zero : (0:ℤ)∈shape m 0 u := Finset.mem_insert_of_mem (Finset.mem_Icc.mpr (by omega))
            have member : affine r d 0∈A := by rw [ref]; exact Finset.mem_image_of_mem _ zero
            exact ⟨_,member⟩
          · exact isAP_nonempty (legal.2 A hA S hs same)
        obtain ⟨z,hz⟩ := meet
        obtain ⟨i,_,ei⟩ := Finset.mem_image.mp (ref ▸ (Finset.mem_inter.mp hz).1)
        obtain ⟨j,_,ej⟩ := Finset.mem_image.mp (eqn ▸ (Finset.mem_inter.mp hz).2)
        have base : a=r+d*(i-j) := by dsimp [affine] at ei ej; linear_combination ej-ei
        exact ⟨i-j,t,fun _ => ⟨low,high,eqn.trans (base ▸ rebase r d (i-j) m t)⟩⟩
      · exact ⟨0,0,fun h => (hs h).elim⟩
    choose c t spec using relative
    apply normalized (c:=c) (t:=t) top (fun S hs => ⟨(spec S hs).1,(spec S hs).2.1⟩)
    intro S hs P hp neq
    have inj : Function.Injective (affine r d) := by
      intro x y he
      dsimp [affine] at he
      exact mul_left_cancel₀ hd (by linarith only [he])
    apply signed_pull (r:=r) hd
    change IsAP ((shape m (c S) (t S) ∩ shape m (c P) (t P)).image (affine r d))
    rw [Finset.image_inter _ _ inj]
    exact congrArg₂ (fun U V => IsAP (U∩V)) (spec S hs).2.2 (spec P hp).2.2 ▸ legal.2 S hs P hp neq
  · simp [Finset.not_nonempty_iff_eq_empty.mp ne]

/-- The physical diameter restricts the step even after translating the support. -/
theorem physical_width {m t N : ℕ} {a d j : ℤ}
    (support : mapSet a d (shape m 0 t) ⊆ Finset.Icc (j+1) (j+N)) :
    d.natAbs*(m+t)≤N-1 := by
  have hi : (m:ℤ)∈shape m 0 t := Finset.mem_insert_of_mem (Finset.mem_Icc.mpr (by omega))
  have lo : (0:ℤ)-t∈shape m 0 t := Finset.mem_insert_self _ _
  have upper := Finset.mem_Icc.mp (support (Finset.mem_image_of_mem (affine a d) hi))
  have lower := Finset.mem_Icc.mp (support (Finset.mem_image_of_mem (affine a d) lo))
  have diff : affine a d (m:ℤ)-affine a d (0-(t:ℤ))=d*((m:ℤ)+t) := by dsimp [affine]; ring
  have bound : (d*((m:ℤ)+t)).natAbs≤N-1 := by rw [←diff]; omega
  simpa only [Int.natAbs_mul,←Nat.cast_add,Int.natAbs_natCast] using bound

def fits (S : Finset ℤ) (m T : ℕ) (d : ℤ) : Prop :=
  ∃ a : ℤ, ∃ t : ℕ, 2≤t ∧ t≤T ∧ S=mapSet a d (shape m 0 t)

private theorem sliced {N m T e : ℕ} {F : Finset (Finset ℤ)} {d j : ℤ}
    (legal : Legal (Finset.Icc (j+1) (j+N)) F) (ed : d.natAbs=e) (pos : 0<e) (top : T≤m) :
    (F.filter (fun S => fits S m T d)).card≤oneSide m (min T ((N-1)/e-m)) := by
  let G := F.filter fun S => fits S m T d
  have sub : G⊆F := Finset.filter_subset _ _
  have hG : Legal _ G := ⟨fun S hs => legal.1 S (sub hs),fun S hs P hp => legal.2 S (sub hs) P (sub hp)⟩
  apply fixed_step hG (show d≠0 by intro h; simp [h] at ed; omega) ((min_le_left _ _).trans top)
  intro S hs
  obtain ⟨a,t,low,high,eqn⟩ := (Finset.mem_filter.mp hs).2
  have span := physical_width (eqn ▸ legal.1 S (sub hs))
  rw [ed,Nat.mul_comm] at span
  have len := (Nat.le_div_iff_mul_le pos).mpr span
  have ht : t≤min T ((N-1)/e-m) := le_min high (by omega)
  exact ⟨a,t,by exact_mod_cast low,by exact_mod_cast ht,eqn⟩

/-- Pay both orientations once per feasible positive step on the actual support.
No uniqueness of a maximum-core representation is needed. -/
theorem actual {N m T : ℕ} {j : ℤ} {F G : Finset (Finset ℤ)}
    (legal : Legal (Finset.Icc (j+1) (j+N)) F) (sub : G⊆F) (top : T≤m)
    (repr : ∀ S∈G, ∃ d : ℕ, 0<d ∧ (fits S m T d ∨ fits S m T (-(d:ℤ)))) :
    G.card≤∑ d ∈ Finset.Icc 1 ((N-1)/(m+2)), 2*oneSide m (min T ((N-1)/d-m)) := by
  classical
  let side (d : ℤ) := F.filter fun S => fits S m T d
  let steps := Finset.Icc 1 ((N-1)/(m+2))
  have cover : G⊆steps.biUnion (fun d => side d ∪ side (-(d:ℤ))) := by
    intro S hs
    obtain ⟨d,hd,rep⟩ := repr S hs
    have bound (e : ℤ) (abs : e.natAbs=d) (fit : fits S m T e) : d∈steps := by
      obtain ⟨a,t,low,_,eqn⟩ := fit
      have span := physical_width (eqn ▸ legal.1 S (sub hs))
      rw [abs] at span
      exact Finset.mem_Icc.mpr ⟨hd,(Nat.le_div_iff_mul_le (by omega)).mpr
        ((Nat.mul_le_mul_left d (by omega : m+2≤m+t)).trans span)⟩
    rcases rep with left | right
    · exact Finset.mem_biUnion.mpr ⟨d,bound d (by simp) left,
        Finset.mem_union_left _ (Finset.mem_filter.mpr ⟨sub hs,left⟩)⟩
    · exact Finset.mem_biUnion.mpr ⟨d,bound (-(d:ℤ)) (by simp) right,
        Finset.mem_union_right _ (Finset.mem_filter.mpr ⟨sub hs,right⟩)⟩
  apply (Finset.card_le_card cover).trans (Finset.card_biUnion_le.trans ?_)
  apply Finset.sum_le_sum
  intro d hd
  have pos := (Finset.mem_Icc.mp hd).1
  exact (Finset.card_union_le _ _).trans (by
    rw [two_mul]
    exact Nat.add_le_add (sliced (d:=(d:ℤ)) legal (by simp) pos top)
      (sliced (d:= -(d:ℤ)) legal (by simp) pos top))

#print axioms fixed_step
#print axioms physical_width
#print axioms actual

/-- At any one size all near exterior shapes together cost at most four
members per physical site, independently of the range of strides. -/
theorem four_per_site {N m : ℕ} {F G : Finset (Finset ℤ)}
    (legal : Legal (Ground N) F) (sub : G⊆F)
    (repr : ∀ S∈G, ∃ d : ℕ, 0<d ∧ (fits S m m d ∨ fits S m m (-(d:ℤ)))) :
    G.card≤4*N := by
  have grounded : Legal (Finset.Icc ((0:ℤ)+1) (0+N)) F :=
    ⟨fun S hs z hz => Finset.mem_Icc.mpr (by simpa using (mem_ground N z).mp (legal.1 S hs hz)),legal.2⟩
  have counted := actual grounded sub (le_refl m) repr
  let D := (N-1)/(m+2)
  have bound (d : ℕ) : 2*oneSide m (min m ((N-1)/d-m))≤4*(m+2) := by
    have le := min_le_left m ((N-1)/d-m)
    unfold oneSide
    split_ifs <;> omega
  have sum := Finset.sum_le_sum (s:=Finset.Icc 1 D) (fun d _ => bound d)
  have card : (Finset.Icc 1 D).card=D := by simp [Nat.card_Icc]
  simp only [Finset.sum_const,card,smul_eq_mul] at sum
  have last : D*(m+2)≤N-1 := Nat.div_mul_le_self _ _
  exact counted.trans (sum.trans (by nlinarith only [last,Nat.sub_le N 1]))

#print axioms four_per_site
end
end JSP233.ExteriorStrides20258
