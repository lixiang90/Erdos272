module

public import Erdos272.Counting.N88404.APClassFrame88404
public import Erdos272.Counting.N20258.RankedPair20258
public import Erdos272.Counting.N20258.MixedOmitter20258
public import Erdos272.Arithmetic.N20258.IntervalGapBounds20258

@[expose] public section
namespace JSP233.IntervalGap20258
open StarCompletion PrivatePairExistence AnchorCompletion38 APClasses88404 AffineLine30
open scoped Classical BigOperators
noncomputable section
set_option autoImplicit false

/-- The two nearest hits enclose a missing interval. Its endpoints recover both hits. -/
private theorem gap_key {M a b : ℤ} (f : ℤ → ℤ)
    (U : Finset (ℤ × ℤ)) (S : Finset ℤ)
    (inBox : ∀ p ∈ U, (1 ≤ p.1 ∧ p.1 ≤ a) ∧ (b ≤ p.2 ∧ p.2 ≤ M))
    (ends : ∃ p ∈ U, p.2 = b) (starts : ∃ p ∈ U, p.1 = a)
    (hits : ∀ p ∈ U, ∃ t ∈ Finset.Icc p.1 p.2, f t ∈ S)
    (miss : ¬ ∃ t ∈ Finset.Icc a b, f t ∈ S) :
    ∃ p ∈ (Finset.Icc 1 a ×ˢ Finset.Icc b M) \ U, f (p.1-1) ∈ S ∧ f (p.2+1) ∈ S := by
  let L := (Finset.Icc 1 (a-1)).filter fun t => f t ∈ S
  let R := (Finset.Icc (b+1) M).filter fun t => f t ∈ S
  obtain ⟨P,hP,hb⟩ := ends
  obtain ⟨Q,hQ,ha⟩ := starts
  obtain ⟨s,hs,hitS⟩ := hits P hP
  obtain ⟨t,ht,hitT⟩ := hits Q hQ
  have sl := (inBox P hP).1.1
  have tr := (inBox Q hQ).2.2
  obtain ⟨s₁,s₂⟩ := Finset.mem_Icc.mp hs
  obtain ⟨t₁,t₂⟩ := Finset.mem_Icc.mp ht
  have small : s < a := by
    by_contra! h
    exact miss ⟨s,Finset.mem_Icc.mpr ⟨h,by omega⟩,hitS⟩
  have large : b < t := by
    by_contra! h
    exact miss ⟨t,Finset.mem_Icc.mpr ⟨by omega,h⟩,hitT⟩
  have lne : L.Nonempty := ⟨s,Finset.mem_filter.mpr ⟨Finset.mem_Icc.mpr (by omega),hitS⟩⟩
  have rne : R.Nonempty := ⟨t,Finset.mem_filter.mpr ⟨Finset.mem_Icc.mpr (by omega),hitT⟩⟩
  let x := L.max' lne
  let y := R.min' rne
  obtain ⟨xl,hx⟩ := Finset.mem_filter.mp (show x ∈ L from Finset.max'_mem _ _)
  obtain ⟨yr,hy⟩ := Finset.mem_filter.mp (show y ∈ R from Finset.min'_mem _ _)
  obtain ⟨x₁,x₂⟩ := Finset.mem_Icc.mp xl
  obtain ⟨y₁,y₂⟩ := Finset.mem_Icc.mp yr
  have absent : (x+1,y-1) ∉ U := by
    intro hp
    obtain ⟨w,hw,hit⟩ := hits _ hp
    obtain ⟨w₁,w₂⟩ : x+1 ≤ w ∧ w ≤ y-1 := Finset.mem_Icc.mp hw
    by_cases left : w < a
    · have mem : w ∈ L := Finset.mem_filter.mpr ⟨Finset.mem_Icc.mpr (by omega),hit⟩
      have hwx : w ≤ x := Finset.le_max' _ _ mem
      omega
    by_cases right : b < w
    · have mem : w ∈ R := Finset.mem_filter.mpr ⟨Finset.mem_Icc.mpr (by omega),hit⟩
      have hyw : y ≤ w := Finset.min'_le _ _ mem
      omega
    exact miss ⟨w,Finset.mem_Icc.mpr (by omega),hit⟩
  refine ⟨(x+1,y-1),Finset.mem_sdiff.mpr ⟨Finset.mem_product.mpr
    ⟨Finset.mem_Icc.mpr (by dsimp; omega),Finset.mem_Icc.mpr (by dsimp; omega)⟩,absent⟩,?_⟩
  simpa using And.intro hx hy

/-- Count all crooked members against just the unoccupied cells of an endpoint rectangle. -/
private theorem count_rectangle {N m : ℕ} {F G : Finset (Finset ℤ)}
    (legal : Legal (Ground N) F) (sub : G ⊆ CrookedMembers F)
    {M a b : ℤ} (ab : a ≤ b) (f : ℤ → ℤ) (inj : Function.Injective f)
    (U : Finset (ℤ × ℤ))
    (inBox : ∀ p ∈ U, (1 ≤ p.1 ∧ p.1 ≤ a) ∧ (b ≤ p.2 ∧ p.2 ≤ M))
    (ends : ∃ p ∈ U, p.2 = b) (starts : ∃ p ∈ U, p.1 = a)
    (hits : ∀ S ∈ G, ∀ p ∈ U, ∃ t ∈ Finset.Icc p.1 p.2, f t ∈ S)
    (degree : ∀ t ∈ Finset.Icc a b, (RootPart (CrookedMembers F) (f t)).card ≤ m*(N-2)) :
    G.card + U.card*(N-2) ≤
      ((Finset.Icc a b).card*m + (Finset.Icc 1 a ×ˢ Finset.Icc b M).card)*(N-2) := by
  let K := Finset.Icc a b
  let B := Finset.Icc 1 a ×ˢ Finset.Icc b M
  let H := fun t => RootPart (CrookedMembers F) (f t)
  let V := fun p : ℤ × ℤ => (CrookedMembers F).filter fun S => f (p.1-1) ∈ S ∧ f (p.2+1) ∈ S
  have subset : U ⊆ B := by
    intro p hp
    exact Finset.mem_product.mpr ⟨Finset.mem_Icc.mpr (inBox p hp).1,Finset.mem_Icc.mpr (inBox p hp).2⟩
  have cover : G ⊆ K.biUnion H ∪ (B \ U).biUnion V := by
    intro S hs
    by_cases meet : ∃ t ∈ K, f t ∈ S
    · obtain ⟨t,ht,hit⟩ := meet
      exact Finset.mem_union_left _ (Finset.mem_biUnion.mpr
        ⟨t,ht,Finset.mem_filter.mpr ⟨sub hs,hit⟩⟩)
    obtain ⟨p,hp,hits₂⟩ := gap_key f U S inBox ends starts (hits S hs) meet
    exact Finset.mem_union_right _ (Finset.mem_biUnion.mpr
      ⟨p,hp,Finset.mem_filter.mpr ⟨sub hs,hits₂⟩⟩)
  have leftBound : (K.biUnion H).card ≤ K.card*(m*(N-2)) := by
    apply Finset.card_biUnion_le.trans
    simpa using Finset.sum_le_sum (s := K) degree
  have pairBound (p : ℤ × ℤ) (hp : p ∈ B \ U) : (V p).card ≤ N-2 := by
    obtain ⟨lp,rp⟩ := Finset.mem_product.mp (Finset.mem_sdiff.mp hp).1
    have ha := (Finset.mem_Icc.mp lp).2
    have hb := (Finset.mem_Icc.mp rp).1
    have different : f (p.1-1) ≠ f (p.2+1) := fun eq => by have h := inj eq; omega
    simpa [V] using RankedPair20258.actual_pair legal different ∅ (Finset.empty_subset _)
  have rightBound : ((B \ U).biUnion V).card ≤ (B \ U).card*(N-2) := by
    apply Finset.card_biUnion_le.trans
    simpa using Finset.sum_le_sum pairBound
  have counted := (Finset.card_le_card cover).trans
    ((Finset.card_union_le _ _).trans (Nat.add_le_add leftBound rightBound))
  have eq : ((B \ U).card+U.card)*(N-2) = B.card*(N-2) :=
    congrArg (fun v : ℕ => v*(N-2)) (Finset.card_sdiff_add_card_eq_card subset)
  change G.card+U.card*(N-2) ≤ (K.card*m+B.card)*(N-2)
  rw [Nat.add_mul] at eq
  rw [Nat.add_mul,Nat.mul_assoc]
  omega

/-- For a nonempty actual step class the common interval and its two arms
fit in one residue grid. Each occupied endpoint cell is unavailable to the
crooked members that miss the common interval. -/
theorem actual {N m d : ℕ} {F G : Finset (Finset ℤ)} (hN : 2 ≤ N) (hm : m+1 ≤ N)
    (hd : 0 < d) (legal : Legal (Ground N) F) (sub : G ⊆ CrookedMembers F)
    (active : (StepAP F d).Nonempty)
    (omits : ∀ x ∈ Ground N, ∃ T ∈ F, x ∉ T ∧ T.card ≤ m) :
    ∃ i u v : ℕ, 1 ≤ i ∧ i+u+v ≤ (N-1)/d+1 ∧
      (StepAP F d).card ≤ (u+1)*(v+1) ∧
      G.card + (StepAP F d).card*(N-2) ≤ (i*m+(u+1)*(v+1))*(N-2) := by
  obtain ⟨frame⟩ := APClassFrame88404.frame_nonempty (by omega : 1 ≤ N) hd legal
  let M : ℤ := frame.size
  let z := frame.root
  let f := affine frame.offset (d : ℤ)
  let decode := fun p : ℤ × ℤ => Finset.Icc p.1 p.2
  let U := ((Finset.Icc 1 z) ×ˢ (Finset.Icc z M)).filter fun p => decode p ∈ frame.family
  have hdZ : (0 : ℤ) < d := by exact_mod_cast hd
  have coords {p : ℤ × ℤ} (hp : p ∈ U) :
      (1 ≤ p.1 ∧ p.1 ≤ z) ∧ (z ≤ p.2 ∧ p.2 ≤ M) := by
    obtain ⟨l,r⟩ := Finset.mem_product.mp (Finset.mem_filter.mp hp).1
    exact ⟨Finset.mem_Icc.mp l,Finset.mem_Icc.mp r⟩
  have rep : U.image decode = frame.family := by
    ext S
    constructor
    · rintro hs
      obtain ⟨p,hp,rfl⟩ := Finset.mem_image.mp hs
      exact (Finset.mem_filter.mp hp).2
    · intro hs
      obtain ⟨l,r,eq⟩ := frame.intervals S hs
      subst S
      obtain ⟨lz,zr⟩ : l ≤ z ∧ z ≤ r := Finset.mem_Icc.mp (frame.common_root _ hs)
      have lmem := frame.ground _ hs (Finset.mem_Icc.mpr ⟨le_rfl,lz.trans zr⟩)
      have rmem := frame.ground _ hs (Finset.mem_Icc.mpr ⟨lz.trans zr,le_rfl⟩)
      refine Finset.mem_image.mpr ⟨(l,r),Finset.mem_filter.mpr ⟨Finset.mem_product.mpr
        ⟨Finset.mem_Icc.mpr ⟨((mem_ground _ _).mp lmem).1,lz⟩,
         Finset.mem_Icc.mpr ⟨zr,((mem_ground _ _).mp rmem).2⟩⟩,hs⟩,rfl⟩
  have count : (StepAP F d).card ≤ U.card := by
    rw [← frame.mapped, mapFamily_card _ _ hdZ, ← rep]
    exact Finset.card_image_le
  have une : U.Nonempty := Finset.card_pos.mp ((Finset.card_pos.mpr active).trans_le count)
  obtain ⟨P,hP,top⟩ := Finset.exists_max_image U Prod.fst une
  obtain ⟨Q,hQ,bot⟩ := Finset.exists_min_image U Prod.snd une
  let a := P.1
  let b := Q.2
  have a₁ : 1 ≤ a := (coords hP).1.1
  have ab : a ≤ b := (coords hP).1.2.trans (coords hQ).2.1
  have bM : b ≤ M := (coords hQ).2.2
  have box (p : ℤ × ℤ) (hp : p ∈ U) : (1 ≤ p.1 ∧ p.1 ≤ a) ∧ (b ≤ p.2 ∧ p.2 ≤ M) :=
    ⟨⟨(coords hp).1.1,top p hp⟩,⟨bot p hp,(coords hp).2.2⟩⟩
  have mapped {p : ℤ × ℤ} (hp : p ∈ U) : mapSet frame.offset (d : ℤ) (decode p) ∈ StepAP F d := by
    have mem : mapSet frame.offset (d : ℤ) (decode p) ∈ mapFamily frame.offset (d : ℤ) frame.family :=
      Finset.mem_image.mpr ⟨_,(Finset.mem_filter.mp hp).2,rfl⟩
    rwa [frame.mapped] at mem
  have hits (S : Finset ℤ) (hs : S ∈ G) (p : ℤ × ℤ) (hp : p ∈ U) :
      ∃ t ∈ Finset.Icc p.1 p.2, f t ∈ S := by
    obtain ⟨inF,crooked⟩ := Finset.mem_filter.mp (sub hs)
    have actualP := mapped hp
    have ne : S ≠ mapSet frame.offset (d : ℤ) (decode p) :=
      fun eq => crooked (eq ▸ APClasses88404.is_ap actualP)
    obtain ⟨y,hy⟩ := isAP_nonempty (legal.2 S inF _ (APClasses88404.subset _ _ actualP) ne)
    obtain ⟨inS,inP⟩ := Finset.mem_inter.mp hy
    obtain ⟨t,ht,rfl⟩ := Finset.mem_image.mp inP
    exact ⟨t,ht,inS⟩
  have degree (t : ℤ) (ht : t ∈ Finset.Icc a b) :
      (RootPart (CrookedMembers F) (f t)).card ≤ m*(N-2) := by
    have mem : t ∈ decode P := Finset.mem_Icc.mpr
      ⟨(Finset.mem_Icc.mp ht).1,(Finset.mem_Icc.mp ht).2.trans (bot P hP)⟩
    have phys := legal.1 _ (APClasses88404.subset _ _ (mapped hP)) (Finset.mem_image.mpr ⟨t,mem,rfl⟩)
    obtain ⟨T,hT,miss,small⟩ := omits _ phys
    have price := (MixedOmitter20258.actual_degree legal hT miss).trans
      (SparseSmall39.degreeBudget_mono N small)
    rw [← SparseSmall39.degreeBudget_closed N m hN hm]
    exact price.trans (Nat.le_add_right _ _)
  have cap := count_rectangle legal sub ab f (affine_injective _ _ hdZ) U box
    ⟨Q,hQ,rfl⟩ ⟨P,hP,rfl⟩ hits degree
  have rectangle : U ⊆ (Finset.Icc 1 a ×ˢ Finset.Icc b M) := fun p hp =>
    Finset.mem_product.mpr ⟨Finset.mem_Icc.mpr (box p hp).1,Finset.mem_Icc.mpr (box p hp).2⟩
  have rect := count.trans (Finset.card_le_card rectangle)
  rw [Finset.card_product,Int.card_Icc,Int.card_Icc] at rect
  rw [Finset.card_product,Int.card_Icc,Int.card_Icc,Int.card_Icc] at cap
  let i := (b-a+1).toNat
  let u := (a-1).toNat
  let v := (M-b).toNat
  have wl : (a+1-1).toNat = u+1 := by dsimp [u]; omega
  have wr : (M+1-b).toNat = v+1 := by dsimp [v]; omega
  have wi : (b+1-a).toNat = i := by dsimp [i]; omega
  rw [wl,wr] at rect
  rw [wl,wr,wi] at cap
  have len : frame.size-1 ≤ (N-1)/d := by
    apply (Nat.le_div_iff_mul_le hd).mpr
    have s : ((frame.size-1 : ℕ) : ℝ)*(d : ℝ) ≤ ((N-1 : ℕ) : ℝ) := by
      rw [Nat.cast_sub frame.size_positive,Nat.cast_sub (by omega : 1 ≤ N),Nat.cast_one,mul_comm]
      exact frame.span
    exact_mod_cast s
  have same : i+u+v = frame.size := by dsimp [i,u,v,M] at *; omega
  exact ⟨i,u,v,by dsimp [i]; omega,by omega,rect,
    (Nat.add_le_add_left (Nat.mul_le_mul_right _ count) _).trans cap⟩

#print axioms actual

/-- Three integer evaluations bound an entire actual class, including an empty class. -/
theorem actual_limit {N m d L : ℕ} {F G : Finset (Finset ℤ)}
    (hN : 3 ≤ N) (hm : 0 < m) (room : m+1 ≤ N) (hd : 0 < d) (level : m ≤ L)
    (legal : Legal (Ground N) F) (sub : G ⊆ CrookedMembers F) (many : L*(N-2) < G.card)
    (omits : ∀ x ∈ Ground N, ∃ T ∈ F, x ∉ T ∧ T.card ≤ m) :
    4*((StepAP F d).card : ℤ) ≤ IntervalGapBounds20258.limit ((N-1)/d+1) m L := by
  by_cases active : (StepAP F d).Nonempty
  · obtain ⟨i,u,v,one,size,rect,joint⟩ := actual (by omega) room hd legal sub active omits
    have dpos : 0 < N-2 := by omega
    have pay := IntervalGapBounds20258.rectangle
      (by exact_mod_cast dpos : (0 : ℤ) < (N-2 : ℕ))
      (Int.natCast_nonneg u) (Int.natCast_nonneg v)
      (by exact_mod_cast size : (i : ℤ)+u+v ≤ ((N-1)/d+1 : ℕ))
      (by exact_mod_cast many : (L : ℤ)*(N-2 : ℕ) < G.card)
      (by exact_mod_cast rect : ((StepAP F d).card : ℤ) ≤ ((u : ℤ)+1)*((v : ℤ)+1))
      (by exact_mod_cast joint : (G.card : ℤ)+((StepAP F d).card : ℤ)*(N-2 : ℕ) ≤
        ((i : ℤ)*m+((u : ℤ)+1)*((v : ℤ)+1))*(N-2 : ℕ))
    exact pay.trans (IntervalGapBounds20258.score_le_limit hm level one (by omega))
  · rw [Finset.not_nonempty_iff_eq_empty.mp active]
    simp only [Finset.card_empty,Nat.cast_zero,mul_zero]
    exact IntervalGapBounds20258.limit_nonneg _ _ _

#print axioms actual_limit

end
end JSP233.IntervalGap20258
