module

public import Erdos272.Arithmetic.N20258.PopulationChecks20258
public import Erdos272.Capacity.N20258.NaturalPopulation20258

@[expose] public section
namespace JSP233.PopulationFloors20258
open PopulationChecks20258 PopulationPrice20258 PopulationTariff20258 IndividualPrice20258 NaturalPopulation20258
set_option autoImplicit false

structure Floor where
  eval : ℕ → ℕ → ℕ
  bound : ∀ s e,eval s e≤value s e

def select (boundary : ℕ) (left right : Floor) : Floor where
  eval s e := if s<boundary then left.eval s e else right.eval s e
  bound s e := by split <;> first | exact left.bound s e | exact right.bound s e

structure Grid where
  start : ℕ
  defects : ℕ
  rows : List (List ℕ)

def Grid.raw (g : Grid) (i j : ℕ) := ((g.rows[i]?).getD [])[j]?.getD 0

def Grid.check (g : Grid) := (List.range g.rows.length).all (fun i => (List.range g.defects).all
  (fun j => paid ⟨0,0,0,g.raw i j,1,[]⟩ (g.start+i) (j+1)))

def Grid.floor (g : Grid) (check : g.check=true) : Floor where
  eval s e := if g.start≤s ∧ s-g.start<g.rows.length ∧ 0<e ∧ e≤g.defects then g.raw (s-g.start) (e-1) else 0
  bound s e := by
    split
    · next h =>
        obtain ⟨low,si,pos,ej⟩ := h
        have a := (List.all_eq_true.mp check) (s-g.start) (List.mem_range.mpr si)
        have b := (List.all_eq_true.mp a) (e-1) (List.mem_range.mpr (by omega))
        simpa only [Cell,grant,List.map_nil,List.sum_nil,Nat.one_mul,Nat.add_zero,
          show g.start+(s-g.start)=s by omega,show e-1+1=e by omega] using paid_sound b
    · exact Nat.zero_le _

def cell (p : Plan) (r : Extras) (u s e : ℕ) : Prop :=
  let w := grant p.table s e
  if e=1 then (p.scale*p.head≤p.scale*(max u (natural s))+w ∧ p.scale*p.head≤p.scale*u+w+extra r s)
  else p.scale*p.head≤p.scale*u+w

instance (p : Plan) (r : Extras) (u s e : ℕ) : Decidable (cell p r u s e) := by unfold cell; infer_instance

private theorem grow {p : Plan} {r : Extras} {u v s e : ℕ} (le : u≤v) (lower : cell p r u s e) : cell p r v s e := by
  have paid := Nat.mul_le_mul_left p.scale le
  have raised := Nat.mul_le_mul_left p.scale (max_le_max_right (natural s) le)
  by_cases one : e=1 <;> simp only [cell,one,ite_true,ite_false] at lower ⊢ <;> omega

def Window (p : Plan) (r : Extras) (a b : ℕ) : Prop :=
  ∀ s : ℕ,a≤s → s≤b → ∀ j : Fin (p.stop-1), cell p r (value s (j.val+1)) s (j.val+1)

private theorem covered {p : Plan} {r : Extras} {u s e : ℕ} (paid : p.head≤u) : cell p r u s e := by
  have whole := Nat.mul_le_mul_left p.scale paid
  have raised := Nat.mul_le_mul_left p.scale (paid.trans (le_max_left u (natural s)))
  unfold cell
  split <;> omega

def enough (p : Plan) (r : Extras) (u s e : ℕ) :=
  decide (p.head≤u) || decide (cell p r u s e)

def check (g : Floor) (p : Plan) (r : Extras) (a b : ℕ) := (List.range (b+1-a)).all (fun i =>
  (List.range (p.stop-1)).all (fun j => enough p r (g.eval (a+i) (j+1)) (a+i) (j+1)))

theorem window {g : Floor} {p : Plan} {r : Extras} {a b : ℕ} (checked : check g p r a b=true) : Window p r a b := by
  intro s lo hi j
  have row := (List.all_eq_true.mp checked) (s-a) (List.mem_range.mpr (by omega))
  have point := (List.all_eq_true.mp row) j.val (List.mem_range.mpr j.isLt)
  rw [show a+(s-a)=s by omega] at point
  simp only [enough,Bool.or_eq_true,decide_eq_true_eq] at point
  exact grow (g.bound ..) (point.elim covered id)

theorem join {p : Plan} {r : Extras} {a m b : ℕ} (l : Window p r a m) (u : Window p r (m+1) b) : Window p r a b := by
  intro s lo hi j
  by_cases h : s≤m
  · exact l s lo h j
  · exact u s (by omega) hi j

theorem certify {p : Plan} {r : Extras} (shape : Shape p) (sizes : ∀ z∈r,3≤z.1)
    (cells : Window p r p.minimum p.top) : Good p r := by
  obtain ⟨a,b,c,d,e,f,g⟩ := shape
  refine ⟨a,b,c,d,e,sizes,f,g,?_⟩
  intro i j
  exact cells _ (Nat.le_add_right ..) (by have := i.isLt; omega) j

theorem ordinary {p : Plan} (good : Good p []) : p.Valid := by
  obtain ⟨a,b,c,d,e,_,f,g,cells⟩ := good
  refine ⟨a,b,c,d,e,f,g,?_⟩
  intro i j
  have paid := cells i j
  dsimp only at paid
  by_cases one : j.val+1=1
  · rw [ite_eq_left one] at paid
    simpa only [extra,List.map_nil,List.sum_nil,Nat.add_zero] using paid.2
  · rwa [ite_eq_right one] at paid

#print axioms Grid.floor
#print axioms certify
end JSP233.PopulationFloors20258
