module

public import Erdos272.Arithmetic.APInterval208

@[expose] public section

namespace JSP233.APReflection86412
open ActualAPCount208 APInterval208 PureSource208
open scoped Classical
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1000000

def NegSet (S : Finset ℤ) : Finset ℤ := S.image (fun x => -x)

def ReflectCode (q : ℕ) (p : ℤ×ℤ) : ℤ×ℤ :=
  let d := p.2-p.1
  ((q : ℤ)*d-p.2-d, (q : ℤ)*d-p.2)

theorem mem_negset {S : Finset ℤ} {x : ℤ} : x∈NegSet S ↔ -x∈S := by
  constructor
  · intro hx
    obtain ⟨y, hy, rfl⟩ := Finset.mem_image.mp hx
    simpa only [neg_neg] using hy
  · intro hx
    exact Finset.mem_image.mpr ⟨-x, hx, by ring⟩

theorem negset_negset (S : Finset ℤ) : NegSet (NegSet S)=S := by
  ext x
  rw [mem_negset, mem_negset, neg_neg]

theorem card_negset (S : Finset ℤ) : (NegSet S).card=S.card := by
  exact Finset.card_image_of_injective S (fun x y h => by omega)

theorem reflect_involution (q : ℕ) (p : ℤ×ℤ) :
    ReflectCode q (ReflectCode q p)=p := by
  apply Prod.ext <;> dsimp only [ReflectCode] <;> ring

theorem reflect_injective (q : ℕ) : Function.Injective (ReflectCode q) := by
  intro p r he
  have hh := congrArg (ReflectCode q) he
  simpa only [reflect_involution] using hh

theorem point_reflect {q j : ℕ} (p : ℤ×ℤ) (hj : j≤q) :
    Point (ReflectCode q p) j = -Point p (q-j) := by
  dsimp only [Point, ReflectCode]
  rw [Nat.cast_sub hj]
  ring

theorem reflect_mem_codes {S : Finset ℤ} {q : ℕ} (hq : 1≤q)
    {p : ℤ×ℤ} (hp : p∈Codes S q) : ReflectCode q p∈Codes (NegSet S) q := by
  obtain ⟨hx, hy, hxy, hall⟩ := mem_codes.mp hp
  have hpoint : ∀ j≤q, Point (ReflectCode q p) j∈NegSet S := by
    intro j hj
    apply mem_negset.mpr
    rw [point_reflect p hj, neg_neg]
    exact hall (q-j) (Nat.sub_le _ _)
  apply mem_codes.mpr
  refine ⟨?_, ?_, ?_, hpoint⟩
  · simpa only [point_one] using hpoint 1 hq
  · simpa only [point_zero] using hpoint 0 (by omega)
  · dsimp only [ReflectCode]
    omega

theorem codes_negset_image {S : Finset ℤ} {q : ℕ} (hq : 1≤q) :
    (Codes S q).image (ReflectCode q)=Codes (NegSet S) q := by
  ext p
  constructor
  · intro hp
    obtain ⟨r, hr, rfl⟩ := Finset.mem_image.mp hp
    exact reflect_mem_codes hq hr
  · intro hp
    have hr : ReflectCode q p∈Codes S q := by
      simpa only [negset_negset] using reflect_mem_codes hq hp
    exact Finset.mem_image.mpr ⟨ReflectCode q p, hr, reflect_involution q p⟩

theorem count_reflection {S : Finset ℤ} {q : ℕ} (hq : 1≤q) :
    (Codes (NegSet S) q).card=(Codes S q).card := by
  rw [←codes_negset_image hq, Finset.card_image_of_injective _ (reflect_injective q)]

theorem optimal_reflection {S : Finset ℤ} {q : ℕ} (hq : 1≤q)
    (heq : (Codes S q).card=intervalMultiplicity S.card q) :
    (Codes (NegSet S) q).card=intervalMultiplicity (NegSet S).card q := by
  rw [count_reflection hq, card_negset]
  exact heq

#print axioms mem_negset
#print axioms negset_negset
#print axioms card_negset
#print axioms reflect_involution
#print axioms reflect_injective
#print axioms point_reflect
#print axioms reflect_mem_codes
#print axioms codes_negset_image
#print axioms count_reflection
#print axioms optimal_reflection
end
end JSP233.APReflection86412
