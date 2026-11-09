module

public import Lean

@[expose] public section

/-!
Actual arithmetic-progression union and private-point mechanisms, round 21.

The sets are predicates on the integers.  `APAt d p S` means exactly the
intersection of one finite integer interval and the residue class of `p`
modulo the positive integer `d`; it is not an abstract closure hypothesis.
The main theorem proves private points outside an actual AP core trace from
same-step AP pair traces.  No extremal cardinality theorem is assumed.
-/

namespace JSP233.PrivateUnion

def APAt (d p : Int) (S : Int → Prop) : Prop :=
  0 < d ∧ ∃ lo hi : Int, ∀ x,
    S x ↔ lo ≤ x ∧ x ≤ hi ∧ d ∣ x - p

def IsAP (S : Int → Prop) : Prop :=
  ∃ d p : Int, APAt d p S ∧ S p

theorem APAt_rebase (d p u : Int) (S : Int → Prop)
    (hS : APAt d p S) (hu : S u) : APAt d u S := by
  rcases hS with ⟨hd, lo, hi, hrep⟩
  have hdu := ((hrep u).mp hu).2.2
  refine ⟨hd, lo, hi, ?_⟩
  intro x
  constructor
  · intro hx
    have hx' := (hrep x).mp hx
    have hsub := Int.dvd_sub hx'.2.2 hdu
    have he : (x-p)-(u-p)=x-u := by omega
    rw [he] at hsub
    exact ⟨hx'.1, hx'.2.1, hsub⟩
  · intro hx
    have hadd := Int.dvd_add hx.2.2 hdu
    have he : (x-u)+(u-p)=x-p := by omega
    rw [he] at hadd
    exact (hrep x).mpr ⟨hx.1, hx.2.1, hadd⟩

/-- An AP containing an actual adjacent pair of a larger set has exactly
the gap of that pair as step.  Thus same-step pair traces can be derived,
rather than postulated, in the thin-fringe application. -/
theorem APAt_step_eq_of_adjacent (q r u d : Int) (T : Int → Prop)
    (hd : 0 < d) (hT : APAt q r T) (hu : T u) (hv : T (u+d))
    (hgap : ∀ x, u < x → x < u+d → ¬ T x) : q = d := by
  rcases hT with ⟨hq, lo, hi, hrep⟩
  have hu' := (hrep u).mp hu
  have hv' := (hrep (u+d)).mp hv
  have hqd := Int.dvd_sub hv'.2.2 hu'.2.2
  have he : (u+d-r)-(u-r)=d := by omega
  rw [he] at hqd
  have hle := Int.le_of_dvd hd hqd
  by_cases hEq : q = d
  · exact hEq
  · have hlt : q < d := by omega
    have hdiv := Int.dvd_add (Int.dvd_refl q) hu'.2.2
    have hexpr : q+(u-r)=u+q-r := by omega
    rw [hexpr] at hdiv
    have hmid : T (u+q) := (hrep (u+q)).mpr
      ⟨by omega, by omega, hdiv⟩
    exact False.elim (hgap (u+q) (by omega) (by omega) hmid)

theorem IsAP_same_step_of_adjacent (d u : Int) (S T : Int → Prop)
    (hd : 0 < d) (hT : IsAP T) (hu : T u) (hv : T (u+d))
    (hsub : ∀ x, T x → S x)
    (hgap : ∀ x, u < x → x < u+d → ¬ S x) : APAt d u T := by
  rcases hT with ⟨q, r, hT, _⟩
  have hEq := APAt_step_eq_of_adjacent q r u d T hd hT hu hv
    (by intro x hxlo hxhi hx; exact hgap x hxlo hxhi (hsub x hx))
  subst q
  exact APAt_rebase d r u T hT hu

/-- Two finite APs of the same step and with a common point have an AP union.
The interval and divisibility conditions are proved explicitly. -/
theorem union_APAt (d p : Int) (S T : Int → Prop)
    (hS : APAt d p S) (hT : APAt d p T) (hpS : S p) (hpT : T p) :
    APAt d p (fun x => S x ∨ T x) := by
  rcases hS with ⟨hd, a, b, hS⟩
  rcases hT with ⟨_, c, e, hT⟩
  have hpS' := (hS p).mp hpS
  have hpT' := (hT p).mp hpT
  refine ⟨hd, min a c, max b e, ?_⟩
  intro x
  constructor
  · intro hx
    rcases hx with hx | hx
    · have hx' := (hS x).mp hx
      exact ⟨by omega, by omega, hx'.2.2⟩
    · have hx' := (hT x).mp hx
      exact ⟨by omega, by omega, hx'.2.2⟩
  · intro hx
    by_cases hxS : a ≤ x ∧ x ≤ b
    · exact Or.inl ((hS x).mpr ⟨hxS.1, hxS.2, hx.2.2⟩)
    · exact Or.inr ((hT x).mpr ⟨by omega, by omega, hx.2.2⟩)

theorem intersection_APAt (d p : Int) (S T : Int → Prop)
    (hS : APAt d p S) (hT : APAt d p T) :
    APAt d p (fun x => S x ∧ T x) := by
  rcases hS with ⟨hd, a, b, hS⟩
  rcases hT with ⟨_, c, e, hT⟩
  refine ⟨hd, max a c, min b e, ?_⟩
  intro x
  constructor
  · intro hx
    have hxS := (hS x).mp hx.1
    have hxT := (hT x).mp hx.2
    exact ⟨by omega, by omega, hxS.2.2⟩
  · intro hx
    exact ⟨(hS x).mpr ⟨by omega, by omega, hx.2.2⟩,
      (hT x).mpr ⟨by omega, by omega, hx.2.2⟩⟩

theorem APAt_congr (d p : Int) (S T : Int → Prop)
    (hS : APAt d p S) (heq : ∀ x, S x ↔ T x) : APAt d p T := by
  rcases hS with ⟨hd, lo, hi, hrep⟩
  exact ⟨hd, lo, hi, by intro x; rw [← heq x]; exact hrep x⟩

def interWith (S : Int → Prop) : List (Int → Prop) → Int → Prop
  | [] => S
  | T :: ts => fun x => S x ∧ interWith T ts x

theorem mem_interWith (S : Int → Prop) (ts : List (Int → Prop)) (x : Int) :
    interWith S ts x ↔ S x ∧ ∀ T ∈ ts, T x := by
  induction ts generalizing S with
  | nil => simp [interWith]
  | cons T ts ih =>
    change (S x ∧ interWith T ts x) ↔ S x ∧ ∀ U ∈ T :: ts, U x
    rw [ih]
    simp only [List.mem_cons, forall_eq_or_imp]

theorem interWith_APAt (d p : Int) (S : Int → Prop)
    (ts : List (Int → Prop)) (hS : APAt d p S)
    (hTs : ∀ T ∈ ts, APAt d p T) : APAt d p (interWith S ts) := by
  induction ts generalizing S with
  | nil => exact hS
  | cons T ts ih =>
    have hT := hTs T List.mem_cons_self
    have htail := ih T hT (by
      intro U hU
      exact hTs U (List.mem_cons_of_mem T hU))
    exact intersection_APAt d p S (interWith T ts) hS htail

/-- A finite union with an explicitly included initial set. -/
def unionWith (S : Int → Prop) : List (Int → Prop) → Int → Prop
  | [] => S
  | T :: ts => fun x => S x ∨ unionWith T ts x

theorem mem_unionWith (S : Int → Prop) (ts : List (Int → Prop)) (x : Int) :
    unionWith S ts x ↔ S x ∨ ∃ T ∈ ts, T x := by
  induction ts generalizing S with
  | nil => simp [unionWith]
  | cons T ts ih =>
    change (S x ∨ unionWith T ts x) ↔ S x ∨ ∃ U ∈ T :: ts, U x
    rw [ih]
    simp only [List.mem_cons]
    constructor
    · rintro (hS | hT | ⟨U, hU, hx⟩)
      · exact Or.inl hS
      · exact Or.inr ⟨T, Or.inl rfl, hT⟩
      · exact Or.inr ⟨U, Or.inr hU, hx⟩
    · rintro (hS | ⟨U, hU, hx⟩)
      · exact Or.inl hS
      · rcases hU with rfl | hU
        · exact Or.inr (Or.inl hx)
        · exact Or.inr (Or.inr ⟨U, hU, hx⟩)

theorem unionWith_APAt (d p : Int) (S : Int → Prop)
    (ts : List (Int → Prop))
    (hS : APAt d p S) (hpS : S p)
    (hTs : ∀ T ∈ ts, APAt d p T ∧ T p) :
    APAt d p (unionWith S ts) := by
  induction ts generalizing S with
  | nil => exact hS
  | cons T ts ih =>
    have hT := hTs T (List.mem_cons_self)
    have hrest : ∀ U ∈ ts, APAt d p U ∧ U p := by
      intro U hU
      exact hTs U (List.mem_cons_of_mem T hU)
    have htail := ih T hT.1 hT.2 hrest
    have hptail : unionWith T ts p :=
      (mem_unionWith T ts p).mpr (Or.inl hT.2)
    exact union_APAt d p S (unionWith T ts) hS htail hpS hptail

/-- If a crooked set has an AP core trace and same-step AP intersections
with all other members, it has a point outside the core in no other member.
The finite union closure used in the proof is derived above. -/
theorem private_outside_core (d p : Int) (S K : Int → Prop)
    (others : List (Int → Prop))
    (hcrooked : ¬ IsAP S) (hp : S p ∧ K p)
    (hcore : APAt d p (fun x => S x ∧ K x))
    (htraces : ∀ T ∈ others,
      APAt d p (fun x => S x ∧ T x) ∧ T p) :
    ∃ x, S x ∧ ¬ K x ∧ ∀ T ∈ others, ¬ T x := by
  classical
  apply Classical.byContradiction
  intro hn
  have hcovered : ∀ x, S x → ¬ K x → ∃ T ∈ others, T x := by
    intro x hx hk
    apply Classical.byContradiction
    intro hno
    apply hn
    exact ⟨x, hx, hk, by
      intro T hT hxT
      exact hno ⟨T, hT, hxT⟩⟩
  let traces := others.map (fun T => fun x => S x ∧ T x)
  have hall : ∀ U ∈ traces, APAt d p U ∧ U p := by
    intro U hU
    rcases List.mem_map.mp hU with ⟨T, hT, rfl⟩
    exact ⟨(htraces T hT).1, hp.1, (htraces T hT).2⟩
  have hu := unionWith_APAt d p (fun x => S x ∧ K x) traces hcore hp hall
  have heq : (unionWith (fun x => S x ∧ K x) traces) = S := by
    funext x
    apply propext
    rw [mem_unionWith]
    constructor
    · rintro (hx | ⟨U, hU, hx⟩)
      · exact hx.1
      · rcases List.mem_map.mp hU with ⟨T, _, rfl⟩
        exact hx.1
    · intro hx
      by_cases hk : K x
      · exact Or.inl ⟨hx, hk⟩
      · rcases hcovered x hx hk with ⟨T, hT, hxT⟩
        exact Or.inr ⟨(fun y => S y ∧ T y),
          List.mem_map.mpr ⟨T, hT, rfl⟩, hx, hxT⟩
  rw [heq] at hu
  exact hcrooked ⟨d, p, hu, hp.1⟩

def otherIndices {m : Nat} (i : Fin m) : List (Fin m) :=
  (List.finRange m).filter (fun j => i ≠ j)

theorem mem_otherIndices {m : Nat} (i j : Fin m) :
    j ∈ otherIndices i ↔ i ≠ j := by
  simp [otherIndices]

/-- The actual common kernel of at least two members is an AP of the same
step as all pair intersections.  No AP hypothesis on the kernel is needed. -/
theorem common_kernel_APAt {m : Nat} (d p : Int)
    (F : Fin m → Int → Prop) (i j : Fin m) (hij : i ≠ j)
    (hpair : ∀ a b, a ≠ b → APAt d p (fun x => F a x ∧ F b x)) :
    APAt d p (fun x => ∀ a, F a x) := by
  let traces := (otherIndices i).map (fun a => fun x => F i x ∧ F a x)
  have ht : ∀ T ∈ traces, APAt d p T := by
    intro T hT
    rcases List.mem_map.mp hT with ⟨a, ha, rfl⟩
    exact hpair i a ((mem_otherIndices i a).mp ha)
  have hap := interWith_APAt d p (fun x => F i x ∧ F j x)
    traces (hpair i j hij) ht
  apply APAt_congr d p _ _ hap
  intro x
  rw [mem_interWith]
  constructor
  · intro hx a
    by_cases ha : i = a
    · subst a
      exact hx.1.1
    · have hmem : (fun y => F i y ∧ F a y) ∈ traces :=
        List.mem_map.mpr ⟨a, (mem_otherIndices i a).mpr ha, rfl⟩
      exact (hx.2 _ hmem).2
  · intro hx
    refine ⟨⟨hx i, hx j⟩, ?_⟩
    intro T hT
    rcases List.mem_map.mp hT with ⟨a, _, rfl⟩
    exact ⟨hx i, hx a⟩

/-- A finite indexed family of actual crooked integer sets gets an injective
assignment of core-exterior private points, under the common-step trace
hypotheses.  The shared point and core may vary neither with i nor with j. -/
theorem private_selection {m : Nat} (d p : Int)
    (F : Fin m → Int → Prop) (K : Int → Prop)
    (hcrooked : ∀ i, ¬ IsAP (F i))
    (hpK : K p) (hpF : ∀ i, F i p)
    (hcore : ∀ i, APAt d p (fun x => F i x ∧ K x))
    (hpair : ∀ i j, i ≠ j → APAt d p (fun x => F i x ∧ F j x)) :
    ∃ f : Fin m → Int,
      (∀ i, F i (f i) ∧ ¬ K (f i)) ∧
      (∀ i j, i ≠ j → ¬ F j (f i)) ∧
      (∀ i j, f i = f j → i = j) := by
  classical
  have hex : ∀ i, ∃ x, F i x ∧ ¬ K x ∧ ∀ j, i ≠ j → ¬ F j x := by
    intro i
    let others := (otherIndices i).map F
    have ht : ∀ T ∈ others,
        APAt d p (fun x => F i x ∧ T x) ∧ T p := by
      intro T hT
      rcases List.mem_map.mp hT with ⟨j, hj, rfl⟩
      exact ⟨hpair i j ((mem_otherIndices i j).mp hj), hpF j⟩
    rcases private_outside_core d p (F i) K others
      (hcrooked i) ⟨hpF i, hpK⟩ (hcore i) ht with ⟨x, hx, hk, hpriv⟩
    refine ⟨x, hx, hk, ?_⟩
    intro j hij
    exact hpriv (F j) (List.mem_map.mpr
      ⟨j, (mem_otherIndices i j).mpr hij, rfl⟩)
  let f := fun i => Classical.choose (hex i)
  have hf := fun i => Classical.choose_spec (hex i)
  refine ⟨f, ?_, ?_, ?_⟩
  · intro i
    exact ⟨(hf i).1, (hf i).2.1⟩
  · intro i j hij
    exact (hf i).2.2 j hij
  · intro i j heq
    apply Classical.byContradiction
    intro hij
    have hnot := (hf i).2.2 j hij
    have hj : F j (f j) := (hf j).1
    rw [← heq] at hj
    exact hnot hj

theorem nodup_ofFn_of_injective {α : Type} {m : Nat} (f : Fin m → α)
    (hinj : ∀ i j, f i = f j → i = j) : (List.ofFn f).Nodup := by
  apply List.pairwise_iff_getElem.mpr
  intro i j hi hj hij heq
  simp only [List.getElem_ofFn] at heq
  have hfin := hinj ⟨i, by simpa using hi⟩ ⟨j, by simpa using hj⟩ heq
  have hval := congrArg Fin.val hfin
  change i = j at hval
  omega

/-- A local list-capacity proof, kept independent of a library theorem
introduced after Lean 4.32.2.  Each distinct head removes one actual slot. -/
theorem list_nodup_length_le_of_subset {α : Type} {left right : List α}
    (hnd : left.Nodup) (hsub : left ⊆ right) : left.length ≤ right.length := by
  classical
  induction left generalizing right with
  | nil => simp
  | cons a xs ih =>
    have hnot := (List.nodup_cons.mp hnd).1
    have hxsnd := (List.nodup_cons.mp hnd).2
    have ha : a ∈ right := hsub List.mem_cons_self
    have hxs : xs ⊆ right.erase a := by
      intro x hx
      have hne : x ≠ a := by
        intro heq
        subst x
        exact hnot hx
      exact (List.mem_erase_of_ne hne).mpr
        (hsub (List.mem_cons_of_mem a hx))
    have hlen := ih hxsnd hxs
    have herase := List.length_erase_of_mem ha
    have hpos : 0 < right.length := List.length_pos_of_mem ha
    simp only [List.length_cons]
    omega

/-- The private assignment bounds the number of actual members by any
explicit finite list covering their available exterior points.  The list
need not be a postulated numeric budget: it contains actual integers. -/
theorem family_le_exterior_capacity {m : Nat} (d p : Int)
    (F : Fin m → Int → Prop) (K : Int → Prop) (allowed : List Int)
    (hcrooked : ∀ i, ¬ IsAP (F i))
    (hpK : K p) (hpF : ∀ i, F i p)
    (hcore : ∀ i, APAt d p (fun x => F i x ∧ K x))
    (hpair : ∀ i j, i ≠ j → APAt d p (fun x => F i x ∧ F j x))
    (hallowed : ∀ i x, F i x → ¬ K x → x ∈ allowed) :
    m ≤ allowed.length := by
  rcases private_selection d p F K hcrooked hpK hpF hcore hpair with
    ⟨f, hf, _, hinj⟩
  have hsub : List.ofFn f ⊆ allowed := by
    intro x hx
    rcases List.mem_ofFn.mp hx with ⟨i, rfl⟩
    exact hallowed i (f i) (hf i).1 (hf i).2
  have hlen := list_nodup_length_le_of_subset
    (nodup_ofFn_of_injective f hinj) hsub
  simpa only [List.length_ofFn] using hlen

/-- Round 19's private-point capacity mechanism, now with only ordinary AP
pair traces assumed.  The shared pair is adjacent in every actual member;
the theorem itself forces all intersection steps to be d. -/
theorem family_le_exterior_capacity_of_adjacent {m : Nat} (d u : Int)
    (F : Fin m → Int → Prop) (K : Int → Prop) (allowed : List Int)
    (hd : 0 < d) (hcrooked : ∀ i, ¬ IsAP (F i))
    (huK : K u) (huF : ∀ i, F i u) (hvF : ∀ i, F i (u+d))
    (hgap : ∀ i x, u < x → x < u+d → ¬ F i x)
    (hcore : ∀ i, APAt d u (fun x => F i x ∧ K x))
    (hpair : ∀ i j, i ≠ j → IsAP (fun x => F i x ∧ F j x))
    (hallowed : ∀ i x, F i x → ¬ K x → x ∈ allowed) :
    m ≤ allowed.length := by
  apply family_le_exterior_capacity d u F K allowed hcrooked huK huF hcore
  · intro i j hij
    exact IsAP_same_step_of_adjacent d u (F i) (fun x => F i x ∧ F j x)
      hd (hpair i j hij) ⟨huF i, huF j⟩ ⟨hvF i, hvF j⟩
      (by intro x hx; exact hx.1) (hgap i)
  · exact hallowed

/-- Round 20's common-step, nonempty-common-kernel payment mechanism for
an actual finite integer-set family.  The core is literally the common
intersection of all members, and its AP property is proved, not assumed. -/
theorem family_le_common_kernel_exterior_capacity {m : Nat} (d p : Int)
    (F : Fin m → Int → Prop) (allowed : List Int) (hm : 2 ≤ m)
    (hcrooked : ∀ i, ¬ IsAP (F i)) (hp : ∀ i, F i p)
    (hpair : ∀ i j, i ≠ j → APAt d p (fun x => F i x ∧ F j x))
    (hallowed : ∀ i x, F i x → ¬ (∀ j, F j x) → x ∈ allowed) :
    m ≤ allowed.length := by
  let i : Fin m := ⟨0, by omega⟩
  let j : Fin m := ⟨1, by omega⟩
  have hij : i ≠ j := by intro h; have := congrArg Fin.val h; simp [i, j] at this
  have hk := common_kernel_APAt d p F i j hij hpair
  apply family_le_exterior_capacity d p F (fun x => ∀ a, F a x) allowed
    hcrooked hp hp
  · intro a
    apply APAt_congr d p _ _ hk
    intro x
    exact ⟨fun hx => ⟨hx a, hx⟩, fun hx => hx.2⟩
  · exact hpair
  · exact hallowed

/-- The complete same-step common-kernel payment inequality `h + k <= N`.
Here `h` is the number of actual crooked members, `k` is the length of an
actual duplicate-free list of common points, and `N` is the length of the
actual ground-point list.  No scalar capacity inequality is a premise. -/
theorem family_add_kernel_le_ground_length {m : Nat} (d p : Int)
    (F : Fin m → Int → Prop) (ground core : List Int) (hm : 2 ≤ m)
    (hcrooked : ∀ i, ¬ IsAP (F i)) (hp : ∀ i, F i p)
    (hpair : ∀ i j, i ≠ j → APAt d p (fun x => F i x ∧ F j x))
    (hground : ∀ i x, F i x → x ∈ ground)
    (hcore : ∀ x ∈ core, ∀ i, F i x) (hcore_nodup : core.Nodup) :
    m + core.length ≤ ground.length := by
  let i : Fin m := ⟨0, by omega⟩
  let j : Fin m := ⟨1, by omega⟩
  have hij : i ≠ j := by intro h; have := congrArg Fin.val h; simp [i, j] at this
  have hk := common_kernel_APAt d p F i j hij hpair
  have htrace : ∀ a, APAt d p (fun x => F a x ∧ ∀ b, F b x) := by
    intro a
    apply APAt_congr d p _ _ hk
    intro x
    exact ⟨fun hx => ⟨hx a, hx⟩, fun hx => hx.2⟩
  rcases private_selection d p F (fun x => ∀ a, F a x)
    hcrooked hp hp htrace hpair with ⟨f, hf, _, hinj⟩
  have hnd : (List.ofFn f ++ core).Nodup := by
    apply List.nodup_append.mpr
    refine ⟨nodup_ofFn_of_injective f hinj, hcore_nodup, ?_⟩
    intro x hx y hy heq
    rcases List.mem_ofFn.mp hx with ⟨a, rfl⟩
    apply (hf a).2
    rw [heq]
    exact hcore y hy
  have hsub : List.ofFn f ++ core ⊆ ground := by
    intro x hx
    rcases List.mem_append.mp hx with hx | hx
    · rcases List.mem_ofFn.mp hx with ⟨a, rfl⟩
      exact hground a (f a) (hf a).1
    · exact hground i x (hcore x hx i)
  have hlen := list_nodup_length_le_of_subset hnd hsub
  simpa only [List.length_append, List.length_ofFn] using hlen

#print axioms union_APAt
#print axioms intersection_APAt
#print axioms APAt_congr
#print axioms mem_interWith
#print axioms interWith_APAt
#print axioms APAt_rebase
#print axioms APAt_step_eq_of_adjacent
#print axioms IsAP_same_step_of_adjacent
#print axioms mem_unionWith
#print axioms unionWith_APAt
#print axioms private_outside_core
#print axioms mem_otherIndices
#print axioms common_kernel_APAt
#print axioms private_selection
#print axioms nodup_ofFn_of_injective
#print axioms list_nodup_length_le_of_subset
#print axioms family_le_exterior_capacity
#print axioms family_le_exterior_capacity_of_adjacent
#print axioms family_le_common_kernel_exterior_capacity
#print axioms family_add_kernel_le_ground_length

end JSP233.PrivateUnion
