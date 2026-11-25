module

public import Erdos272.Counting.N20258.CrowdedCores20258
public import Erdos272.Arithmetic.N20258.ConcentratedCharge20258

@[expose] public section
namespace JSP233.PopulationTariff20258
open StarCompletion PrivatePairExistence SourceBridge208
open scoped Classical BigOperators
set_option autoImplicit false

/-- Marks count exterior sites, and the trimmed-core bound counts members.
Only the cost of the former depends on the choice of a closed stride sum. -/
inductive Test
  | marks (minimum k top : ℕ) (closed : Bool)
  | overlap (v a h b : ℕ)
  deriving DecidableEq

def Test.applies : Test → ℕ → ℕ → Prop
  | .marks l k u _, s, e => l≤s ∧ s≤u ∧ e≤k
  | .overlap v a _ b, s, e => s≤v ∧ a≤s-e ∧ s-e≤b

instance (r : Test) (s e : ℕ) : Decidable (r.applies s e) := by cases r <;> unfold Test.applies <;> infer_instance

def Test.unit : Test → ℕ → ℕ
  | .marks .., e => e | .overlap .., _ => 1

def Test.grant (r : Test) (s e : ℕ) := if r.applies s e then r.unit e else 0

def Test.cost (r : Test) (n : ℕ) := match r with
  | .marks l k u closed => if closed then ConcentratedCharge20258.simple n (l-1-k) k u
      else ConcentratedPopulation20258.budget n (l-1-k) k u
  | .overlap _ a h _ => ((n-1)/(a-1))*(n/(a+1-h))

def Test.Valid (r : Test) (m L : ℕ) : Prop := match r with
  | .marks l k _ _ => k+2≤l
  | .overlap v a h b => 1≤h ∧ h≤a ∧ 2≤a ∧
      ∀ j : Fin (b+1-h), (h+j.val)*m+(v-(h+j.val))*(v-(h+j.val))≤L

instance (r : Test) (m L : ℕ) : Decidable (r.Valid m L) := by cases r <;> unfold Test.Valid <;> infer_instance

theorem test_bound {N n m L : ℕ} {F A : Finset (Finset ℤ)} (r : Test)
    (hi : N≤n) (two : 2≤N) (room : m+1≤N) (legal : Legal (Ground N) F) (sub : A⊆F)
    (omits : ∀ x∈Ground N,∃ S∈CrookedMembers F,x∉S ∧ S.card≤m)
    (many : L*(N-2)<(CrookedMembers F).card) (valid : r.Valid m L) :
    ∑ S∈A,r.grant S.card (Defect S)≤r.cost n := by
  classical
  let G := A.filter (fun S => r.applies S.card (Defect S))
  have subG : G⊆F := (Finset.filter_subset _ _).trans sub
  have padded : Legal (Ground n) G := by
    refine ⟨fun S hs x hx => ?_, fun S hs T ht => legal.2 S (subG hs) T (subG ht)⟩
    obtain ⟨l,u⟩ := (mem_ground N x).mp (legal.1 S (subG hs) hx)
    exact (mem_ground n x).mpr ⟨l,u.trans (by exact_mod_cast hi)⟩
  have data (S : Finset ℤ) (hs : S∈G) : r.applies S.card (Defect S) := (Finset.mem_filter.mp hs).2
  simp only [Test.grant,←Finset.sum_filter]
  change ∑ S∈G,r.unit (Defect S)≤r.cost n
  cases r with
  | marks l k top closed =>
    change k+2≤l at valid
    have actual := ConcentratedPopulation20258.actual (a:=l-1-k) (k:=k) (top:=top) padded (by omega)
      (fun S hs => by have := (data S hs).1; omega) (fun S hs => (data S hs).2.1)
      (fun S hs => (data S hs).2.2)
    cases closed with
    | false => exact actual
    | true => exact actual.trans (ConcentratedCharge20258.budget_le (by omega) (by omega))
  | overlap v a h b =>
    obtain ⟨pos,fits,sa,blocked⟩ := valid
    have core (S : Finset ℤ) (hs : S∈G) : a≤MaxAPSize S ∧ MaxAPSize S≤b := by
      have eq : S.card-Defect S=MaxAPSize S := by unfold Defect; have := maxAPSize_le_card S; omega
      simpa only [←eq] using (data S hs).2
    have amount := CrowdedCores20258.actual (m:=m) (L:=L) legal subG two room omits many
      (fun S hs => (data S hs).1) pos fits sa core (by
        intro i low high
        let j : Fin (b+1-h) := ⟨i-h,by omega⟩
        simpa only [show h+j.val=i by dsimp only [j]; omega] using blocked j)
    have lower : (N-1)/(a-1)≤(n-1)/(a-1) := Nat.div_le_div_right (Nat.sub_le_sub_right hi 1)
    have upper : N/(a+1-h)≤n/(a+1-h) := Nat.div_le_div_right hi
    have monotone := Nat.mul_le_mul lower upper
    simpa only [Test.unit,Test.cost,Finset.sum_const,smul_eq_mul,mul_one] using amount.trans monotone

abbrev Table := List (Test × ℕ)

def grant (t : Table) (s e : ℕ) := (t.map (fun (r,w) => w*r.grant s e)).sum

def cost (t : Table) (n : ℕ) := (t.map (fun (r,w) => w*r.cost n)).sum

theorem bill {N n m L : ℕ} {F A : Finset (Finset ℤ)} (t : Table)
    (hi : N≤n) (two : 2≤N) (room : m+1≤N) (legal : Legal (Ground N) F) (sub : A⊆F)
    (omits : ∀ x∈Ground N,∃ S∈CrookedMembers F,x∉S ∧ S.card≤m)
    (many : L*(N-2)<(CrookedMembers F).card) (valid : ∀ t'∈t,t'.1.Valid m L) :
    ∑ S∈A,grant t S.card (Defect S)≤cost t n := by
  classical
  induction t with
  | nil => simp [grant,cost]
  | cons head t ih =>
    obtain ⟨r,w⟩ := head
    have first := test_bound r hi two room legal sub omits many (valid (r,w) (List.mem_cons_self ..))
    simpa only [grant,cost,List.map_cons,List.sum_cons,Finset.sum_add_distrib,←Finset.mul_sum] using
      Nat.add_le_add (Nat.mul_le_mul_left w first) (ih (fun z hz => valid z (List.mem_cons_of_mem _ hz)))

#print axioms bill
end JSP233.PopulationTariff20258
