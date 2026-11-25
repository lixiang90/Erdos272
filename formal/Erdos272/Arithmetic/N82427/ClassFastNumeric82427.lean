module

public import Init

@[expose] public section

namespace JSP233.ClassFastNumeric82427
set_option autoImplicit false
set_option maxRecDepth 10000

def Gate (d : Nat) : Nat :=
  if d%2=0 then 2 else if d%3=0 then 3 else if d%5=0 then 5 else if d%7=0 then 7 else 11

def P2 (t : Nat) : Nat := t/2
def P3 (t : Nat) : Nat := t/3-t/6
def P5 (t : Nat) : Nat := (t/5+t/30)-(t/10+t/15)
def P7 (t : Nat) : Nat := (t/7+t/42+t/70+t/105)-(t/14+t/21+t/35+t/210)

def Prefix (p t : Nat) : Nat := match p with
  | 2 => P2 t
  | 3 => P3 t
  | 5 => P5 t
  | 7 => P7 t
  | 11 => t-(P2 t+P3 t+P5 t+P7 t)
  | _ => 0

def PrefixFacts (p : Nat) : Prop := Prefix p 0=0 ∧
  (List.range 210).all (fun t => decide
    (Prefix p (t+1)=Prefix p t+(if Gate (t+1)=p then 1 else 0)))=true
instance (p : Nat) : Decidable (PrefixFacts p) := by unfold PrefixFacts; infer_instance

def eval (p r n : Nat) : Nat :=
  (r+n)/210*Prefix p 210+Prefix p ((r+n)%210)-Prefix p r

def check (p n b : Nat) : Bool :=
  (List.range 210).all (fun r => decide (b≤eval p r n))

end JSP233.ClassFastNumeric82427
