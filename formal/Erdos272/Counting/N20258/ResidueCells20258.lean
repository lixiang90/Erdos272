module

public import Erdos272.Counting.N88404.ResidueMaps88404

@[expose] public section
namespace JSP233.ResidueCells20258
open StarCompletion OrderedShadow88404 ResidueMaps88404
open scoped Classical
noncomputable section
set_option autoImplicit false

/-! For fixed coarse endpoints, the (i,j) cell has base+q-1-i-j possible
middle positions. Opposite cells have complementary excess. The involution
moves precisely the overflowing ranks into the unused positions there. -/
private def flip (q : ℤ) (v : PointTriple) : PointTriple :=
  (q-1-v.1,q-1-v.2.1,v.2.2+v.1+v.2.1-q+1)

private def pack (q base : ℤ) (v : PointTriple) : PointTriple :=
  if v.2.2 < base+q-1-v.1-v.2.1 then v else flip q v

private def unpack (q base : ℤ) (v : PointTriple) : PointTriple :=
  if v.2.2 < base then v else flip q v

private theorem unpack_pack (q base : ℤ) (v : PointTriple) (top : v.2.2 < base) :
    unpack q base (pack q base v)=v := by
  by_cases h : v.2.2 < base+q-1-v.1-v.2.1
  · simp only [pack,if_pos h,unpack,if_pos top]
  · have other : ¬(flip q v).2.2 < base := by dsimp [flip]; omega
    simp only [pack,if_neg h,unpack,if_neg other]
    apply Prod.ext _ (Prod.ext _ _) <;> dsimp only [flip] <;> omega

private theorem ranges {q base : ℤ} {v : PointTriple} (i : 0 ≤ v.1 ∧ v.1 < q)
    (j : 0 ≤ v.2.1 ∧ v.2.1 < q) (rank : 0 ≤ v.2.2 ∧ v.2.2 < base) :
    let u := pack q base v
    (0 ≤ u.1 ∧ u.1 < q) ∧ (0 ≤ u.2.1 ∧ u.2.1 < q) ∧
      (0 ≤ u.2.2 ∧ u.2.2 < base+q-1-u.1-u.2.1) := by
  dsimp only
  unfold pack
  split
  · omega
  · dsimp only [flip]
    omega

private def width (q : ℕ) (p : PointTriple) := p.2.2-p.1-q
private def args (q : ℕ) (p a : PointTriple) : PointTriple :=
  (a.1,a.2.2,p.2.1-p.1-q+a.2.1)
private def position (q : ℕ) (p a : PointTriple) := pack q (width q p) (args q p a)
private def expand (q : ℕ) (p a : PointTriple) : PointTriple :=
  let w := position q p a
  (p.1+w.1,p.1+w.1+1+w.2.2,p.2.2-w.2.1)

private theorem ranks {M q : ℕ} {r : ℤ} {T : Finset (Finset ℤ)} {p a : PointTriple}
    (hq : 0 < q) (hp : p ∈ ResidueCodes M q r T) (ha : a ∈ Offsets q) :
    0 ≤ (args q p a).2.2 ∧ (args q p a).2.2 < width q p := by
  obtain ⟨hc,phase⟩ := mem_residue.mp hp
  have sort := (mem_codes.mp hc).2.2.2.1
  have left := phase_gap hq phase.1 phase.2.1 sort.1
  have right := phase_gap hq phase.2.1 phase.2.2 sort.2
  have o := (mem_offsets.mp ha).2.1
  dsimp only [args,width]
  omega

/-- A hereditary family of triples contains at least q³ times as many triples
as it contains triples on any one residue class modulo q. -/
theorem upper_exact {M q : ℕ} {r : ℤ} {T : Finset (Finset ℤ)}
    (hq : 0 < q) (carrier : T ⊆ (Ground M).powersetCard 3) (closed : Closed T) :
    (ResidueCodes M q r T).card*q^3 ≤ T.card := by
  let domain := ResidueCodes M q r T ×ˢ Offsets q
  let f := fun w : PointTriple × PointTriple => expand q w.1 w.2
  have bounds (w : PointTriple × PointTriple) (hw : w ∈ domain) :
      let u := position q w.1 w.2
      (0 ≤ u.1 ∧ u.1 < q) ∧ (0 ≤ u.2.1 ∧ u.2.1 < q) ∧
      (0 ≤ u.2.2 ∧ u.2.2 < width q w.1+q-1-u.1-u.2.1) := by
    obtain ⟨hp,ha⟩ := Finset.mem_product.mp hw
    obtain ⟨i,_,j⟩ := mem_offsets.mp ha
    exact ranges i j (ranks hq hp ha)
  have lands : Set.MapsTo f domain (Codes M T) := by
    intro w hw
    have b := bounds w hw
    obtain ⟨hp,_⟩ := Finset.mem_product.mp hw
    apply mem_codes_of_inner closed (mem_residue.mp hp).1
    all_goals dsimp only [f,expand,Sorted,width] at b ⊢ <;> omega
  have inj : Set.InjOn f domain := by
    rintro ⟨p,a⟩ hpa ⟨s,b⟩ hsb eq
    have pa := bounds (p,a) hpa
    have sb := bounds (s,b) hsb
    obtain ⟨hp,ha⟩ := Finset.mem_product.mp hpa
    obtain ⟨hs,hb⟩ := Finset.mem_product.mp hsb
    have hP := (mem_residue.mp hp).2
    have hS := (mem_residue.mp hs).2
    have el := congrArg Prod.fst eq
    have em := congrArg (fun w : PointTriple => w.2.1) eq
    have er := congrArg (fun w : PointTriple => w.2.2) eq
    dsimp only [f,expand] at el em er
    obtain ⟨left,i⟩ := offset_unique hP.1 hS.1 pa.1 sb.1 el
    obtain ⟨right,j⟩ := offset_unique hP.2.2 hS.2.2 sb.2.1 pa.2.1
      (show p.2.2+(position q s b).2.1 = s.2.2+(position q p a).2.1 by omega)
    change p.1 = s.1 at left
    change p.2.2 = s.2.2 at right
    have w : width q p=width q s := by simp only [width,left,right]
    have packed : position q p a=position q s b := Prod.ext i (Prod.ext j.symm (by omega))
    have decoded := congrArg (unpack q (width q p)) packed
    dsimp only [position] at decoded
    rw [unpack_pack q _ _ (ranks hq hp ha).2,w,unpack_pack q _ _ (ranks hq hs hb).2] at decoded
    have a₁ := congrArg Prod.fst decoded
    have a₃ := congrArg (fun v : PointTriple => v.2.1) decoded
    have middle := congrArg (fun v : PointTriple => v.2.2) decoded
    dsimp only [args] at a₁ a₃ middle
    change p.2.1-p.1-q+a.2.1=s.2.1-s.1-q+b.2.1 at middle
    obtain ⟨mid,a₂⟩ := offset_unique hP.2.1 hS.2.1 (mem_offsets.mp ha).2.1 (mem_offsets.mp hb).2.1
      (show p.2.1+a.2.1=s.2.1+b.2.1 by omega)
    exact Prod.ext (Prod.ext left (Prod.ext mid right)) (Prod.ext a₁ (Prod.ext a₂ a₃))
  simpa only [domain,Finset.card_product,offsets_card,codes_card carrier]
    using Finset.card_le_card_of_injOn f lands inj

#print axioms upper_exact
end
end JSP233.ResidueCells20258
