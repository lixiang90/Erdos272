module

public import Erdos272.Capacity.N20258.RootPreparation20258
public import Erdos272.Resources.N291012.RetainedStart291012
public import Erdos272.Resources.ActualExterior208
public import Erdos272.Counting.ShortAP208

@[expose] public section
namespace JSP233.RootAvoidingSteps20258
open StarCompletion APGeometry APCount41 DenseDeletion40
open scoped Classical BigOperators
noncomputable section
set_option autoImplicit false

/-- The size of an actual progression omitting the root bounds its spacing. -/
theorem actual_step_le_ten {N : ℕ} {F : Finset (Finset ℤ)} {c : ℤ} {S : Finset ℤ}
    (lo : 11000 ≤ N) (hi : N < 2^16) (legal : Legal (Ground N) F) (near : B N ≤ F.card)
    (root : ∀ U ∈ Retained N 12 F, ¬IsAP U → c ∈ U)
    (hS : S ∈ F) (ap : IsAP S) (miss : c ∉ S) : Step S ≤ 10 := by
  have large := RootPreparation20258.actual_omitter_size lo hi legal near root hS miss
  have ne := isAP_nonempty ap
  have sub := legal.1 S hS
  have low := (mem_ground N _).mp (sub (low_spec ne).1)
  have high := (mem_ground N _).mp (sub (high_spec ne).1)
  have span := (ShortAP208.actual_root_position sub ap (by omega) (low_spec ne).1).2.2.2
  by_contra h
  have eleven : (11 : ℤ) ≤ Step S := by exact_mod_cast (by omega : 11 ≤ Step S)
  have bound := mul_le_mul_of_nonneg_left eleven (Int.natCast_nonneg (S.card-1))
  omega

/-- An interval that misses the root and reaches the right fringe must start
strictly to the right of the root. Each choice of its two endpoints is unique. -/
private theorem unit_count {N c L R : ℕ} {U : Finset (Finset ℤ)}
    (cl : c ≤ L) (cr : c ≤ R) (rn : R ≤ N)
    (ground : ∀ S ∈ U, S ⊆ Ground N) (miss : ∀ S ∈ U, (c : ℤ) ∉ S)
    (prog : ∀ S ∈ U, IsAP S ∧ Step S = 1)
    (ends : ∀ S ∈ U, Low S ≤ (L : ℤ) ∧ (R : ℤ) ≤ High S) :
    U.card ≤ (L-c)*(N-R+1) := by
  let f (S : Finset ℤ) := (Low S, High S)
  have rep (S : Finset ℤ) (hS : S ∈ U) : ∃ p : ℤ, APAt 1 p S := by
    obtain ⟨_,p,hp⟩ := actual_step (prog S hS).1
    exact ⟨p, by simpa only [(prog S hS).2,Nat.cast_one] using hp⟩
  have maps : Set.MapsTo f (↑U : Set (Finset ℤ))
      ((Finset.Icc ((c : ℤ)+1) (L : ℤ)).product (Finset.Icc (R : ℤ) (N : ℤ))) := by
    intro S hS
    have ne := isAP_nonempty (prog S hS).1
    obtain ⟨p,hp⟩ := rep S hS
    obtain ⟨hl,hr⟩ := ends S hS
    have left : (c : ℤ) < Low S := by
      by_contra h
      exact miss S hS (apAt_fill hp (low_spec ne).1 (high_spec ne).1
        (by omega) (by omega) (one_dvd _))
    have right := (mem_ground N _).mp (ground S hS (high_spec ne).1)
    change (Low S,High S) ∈ (Finset.Icc ((c : ℤ)+1) (L : ℤ)).product (Finset.Icc (R : ℤ) (N : ℤ))
    exact Finset.mem_product.mpr ⟨Finset.mem_Icc.mpr ⟨by omega,hl⟩,
      Finset.mem_Icc.mpr ⟨hr,right.2⟩⟩
  have inj : Set.InjOn f (↑U : Set (Finset ℤ)) := by
    intro S hS T hT eq
    obtain ⟨p,hp⟩ := rep S hS
    obtain ⟨q,hq⟩ := rep T hT
    exact same_step_equal_of_endpoints (d := 1) (isAP_nonempty (prog S hS).1)
      (isAP_nonempty (prog T hT).1) hp hq (congrArg Prod.fst eq) (congrArg Prod.snd eq)
  have left : (Finset.Icc ((c : ℤ)+1) (L : ℤ)).card = L-c := by rw [Int.card_Icc]; omega
  have right : (Finset.Icc (R : ℤ) (N : ℤ)).card = N-R+1 := by rw [Int.card_Icc]; omega
  calc
    U.card ≤ ((Finset.Icc ((c : ℤ)+1) (L : ℤ)).product (Finset.Icc (R : ℤ) (N : ℤ))).card :=
      Finset.card_le_card_of_injOn f maps inj
    _ = _ := by simp [left,right]

private theorem nonunit_count {N L R : ℕ} {U : Finset (Finset ℤ)}
    (rn : R ≤ N) (legal : Legal (Ground N) U)
    (ap : ∀ S ∈ U, IsAP S) (steps : ∀ S ∈ U, Step S ∈ Finset.Icc 2 10)
    (ends : ∀ S ∈ U, Low S ≤ (L : ℤ) ∧ (R : ℤ) ≤ High S) :
    (U.card : ℝ) ≤ (11/20 : ℝ)*L*((N : ℝ)-R)+2*((L : ℝ)+(N-R))+9 := by
  let b : ℝ := (N : ℝ)-R
  let w : ℝ := (L : ℝ)+b
  have b0 : 0 ≤ b := sub_nonneg.mpr (by exact_mod_cast rn)
  have maps : Set.MapsTo Step (↑U : Set (Finset ℤ)) (Finset.Icc 2 10) := steps
  have part : (U.card : ℝ) = ∑ d ∈ Finset.Icc 2 10, ((U.filter (fun S => Step S=d)).card : ℝ) := by
    exact_mod_cast Finset.card_eq_sum_card_fiberwise maps
  have each (d : ℕ) : ((U.filter (fun S => Step S=d)).card : ℝ) ≤
      (L : ℝ)*b/(d : ℝ)^2+w/d+1 := by
    let V := U.filter (fun S => Step S=d)
    have sub : V ⊆ U := Finset.filter_subset _ _
    have legalV : Legal (Ground N) V :=
      ⟨fun S hS => legal.1 S (sub hS),fun S hS T hT => legal.2 S (sub hS) T (sub hT)⟩
    apply ActualExterior208.actual_same_step_endpoint_width rn legalV
      (fun S hS => isAP_nonempty (ap S (sub hS)))
    · intro S hS
      obtain ⟨_,p,hp⟩ := actual_step (ap S (sub hS))
      exact ⟨p, by simpa only [(Finset.mem_filter.mp hS).2] using hp⟩
    · exact fun S hS => ends S (sub hS)
  have I : Finset.Icc 2 10 = ({2,3,4,5,6,7,8,9,10} : Finset ℕ) := by decide
  have quad : (∑ d ∈ Finset.Icc (2 : ℕ) 10, (1 : ℝ)/(d : ℝ)^2) ≤ 11/20 := by rw [I]; norm_num
  have lin : (∑ d ∈ Finset.Icc (2 : ℕ) 10, (1 : ℝ)/(d : ℝ)) ≤ 2 := by rw [I]; norm_num
  have count : (Finset.Icc 2 10 : Finset ℕ).card=9 := by decide
  have sum := Finset.sum_le_sum (s := Finset.Icc 2 10) (fun d _ => each d)
  rw [←part] at sum
  simp only [div_eq_mul_inv,Finset.sum_add_distrib,←Finset.mul_sum,Finset.sum_const,
    nsmul_eq_mul,mul_one,count,Nat.cast_ofNat] at sum
  simp only [one_div] at quad lin
  have q := mul_le_mul_of_nonneg_left quad (mul_nonneg (Nat.cast_nonneg (α := ℝ) L) b0)
  have e := mul_le_mul_of_nonneg_left lin (show 0 ≤ w by dsimp [w]; positivity)
  change _ ≤ 11/20*(L : ℝ)*b+2*w+9
  linarith only [sum,q,e]

private theorem endpoints {N c L R : ℕ} {F : Finset (Finset ℤ)} {P T S : Finset ℤ}
    (g : RootModel291012.Start N c L R F P T)
    (hS : S ∈ F) (ap : IsAP S) (miss : (c : ℤ) ∉ S) :
    Low S ≤ (L : ℤ) ∧ (R : ℤ) ≤ High S := by
  have ret : S ∈ Retained N 12 F :=
    Finset.mem_sdiff.mpr ⟨hS,fun h => (Finset.mem_filter.mp h).2.1 ap⟩
  obtain ⟨⟨x,hx,hxl⟩,y,hy,hry⟩ := g.outside S ret miss
  have ne := isAP_nonempty ap
  exact ⟨((low_spec ne).2 _ hx).trans hxl,hry.trans ((high_spec ne).2 _ hy)⟩

/-- Count the progressions in the original family that omit the retained root,
with the loss from the left endpoint of the unit class kept explicitly. -/
theorem actual_progressions {N c L R : ℕ} {F : Finset (Finset ℤ)} {P T : Finset ℤ}
    (lo : 11000 ≤ N) (hi : N < 2^16) (g : RootModel291012.Start N c L R F P T) :
    ((Avoiders (F.filter IsAP) (c : ℤ)).card : ℝ) ≤
      (31/20 : ℝ)*L*((N : ℝ)-R)-c*((N : ℝ)-R)+3*((L : ℝ)+(N-R))+10 := by
  let A := Avoiders (F.filter IsAP) (c : ℤ)
  let U := A.filter (fun S => Step S=1)
  let V := A.filter (fun S => Step S≠1)
  have mem (S : Finset ℤ) (hS : S ∈ A) : S ∈ F ∧ IsAP S ∧ (c : ℤ) ∉ S := by
    obtain ⟨hAP,hc⟩ := Finset.mem_filter.mp hS
    exact ⟨(Finset.mem_filter.mp hAP).1,(Finset.mem_filter.mp hAP).2,hc⟩
  have ends (S : Finset ℤ) (hS : S ∈ A) : Low S ≤ (L : ℤ) ∧ (R : ℤ) ≤ High S := by
    obtain ⟨hSF,hAP,miss⟩ := mem S hS
    exact endpoints g hSF hAP miss
  have usub : U ⊆ A := Finset.filter_subset _ _
  have vsub : V ⊆ A := Finset.filter_subset _ _
  have u := unit_count g.root_left.le (g.root_left.le.trans g.left_right) g.right_ground
    (fun S hS => g.legal.1 S (mem S (usub hS)).1) (fun S hS => (mem S (usub hS)).2.2)
    (fun S hS => ⟨(mem S (usub hS)).2.1,(Finset.mem_filter.mp hS).2⟩)
    (fun S hS => ends S (usub hS))
  have subF : V ⊆ F := fun _ h => (mem _ (vsub h)).1
  have legalV : Legal (Ground N) V :=
    ⟨fun S hS => g.legal.1 S (subF hS),fun S hS T hT => g.legal.2 S (subF hS) T (subF hT)⟩
  have v := nonunit_count g.right_ground legalV (fun S hS => (mem S (vsub hS)).2.1) (by
    intro S hS
    obtain ⟨hs,ap,miss⟩ := mem S (vsub hS)
    have pos := (actual_step ap).1
    have ne : Step S ≠ 1 := (Finset.mem_filter.mp hS).2
    exact Finset.mem_Icc.mpr ⟨by omega,actual_step_le_ten lo hi g.legal g.near_card g.root hs ap miss⟩)
    (fun S hS => ends S (vsub hS))
  have part : (U.card : ℝ)+V.card=A.card := by
    exact_mod_cast Finset.card_filter_add_card_filter_not (s := A) (fun S => Step S=1)
  have ur : (U.card : ℝ) ≤ ((L : ℝ)-c)*((N : ℝ)-R+1) := by
    have ur' : (U.card : ℝ) ≤ ((L-c)*(N-R+1) : ℕ) := by exact_mod_cast u
    simpa only [Nat.cast_mul,Nat.cast_add,Nat.cast_one,Nat.cast_sub g.root_left.le,
      Nat.cast_sub g.right_ground] using ur'
  have rn : (R : ℝ) ≤ N := by exact_mod_cast g.right_ground
  change (A.card : ℝ) ≤ _
  linarith only [part,ur,v,rn,Nat.cast_nonneg (α := ℝ) c]

theorem actual_unit_progressions {N c L R : ℕ} {F : Finset (Finset ℤ)} {P T : Finset ℤ}
    (g : RootModel291012.Start N c L R F P T)
    (unit : ∀ S ∈ F, IsAP S → (c : ℤ) ∉ S → Step S=1) :
    (Avoiders (F.filter IsAP) (c : ℤ)).card ≤ (L-c)*(N-R+1) := by
  let A := Avoiders (F.filter IsAP) (c : ℤ)
  have data (S : Finset ℤ) (hS : S ∈ A) : S ∈ F ∧ IsAP S ∧ (c : ℤ) ∉ S := by
    obtain ⟨h,miss⟩ := Finset.mem_filter.mp hS
    exact ⟨(Finset.mem_filter.mp h).1,(Finset.mem_filter.mp h).2,miss⟩
  apply unit_count g.root_left.le (g.root_left.le.trans g.left_right) g.right_ground
    (fun S hs => g.legal.1 S (data S hs).1) (fun S hs => (data S hs).2.2)
  · intro S hs
    obtain ⟨h,ap,miss⟩ := data S hs
    exact ⟨ap,unit S h ap miss⟩
  · intro S hs
    obtain ⟨h,ap,miss⟩ := data S hs
    exact endpoints g h ap miss

#print axioms actual_step_le_ten
#print axioms actual_progressions
#print axioms actual_unit_progressions
end
end JSP233.RootAvoidingSteps20258
