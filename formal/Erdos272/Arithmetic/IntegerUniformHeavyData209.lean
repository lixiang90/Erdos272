module

public import Erdos272.Resources.IntegerUniformLight209
public import Erdos272.Arithmetic.IntegerRobustPrices209

@[expose] public section

namespace JSP233.IntegerUniformHeavyData209
open IntegerUniformProfiles209 IntegerUniformRows209 IntegerHighPrices209
open LightClosed208
open scoped Classical BigOperators
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 65536

def T (w : Fin 11) (k : ℕ) (b : Fin 7) : ℕ := (band (row w k) b).T
def E (w : Fin 11) (k : ℕ) (b : Fin 7) : ℕ := (band (row w k) b).E
def U (w : Fin 11) (k : ℕ) (b : Fin 7) : ℕ := (band (row w k) b).U
def B (w : Fin 11) (k : ℕ) (b : Fin 7) : ℕ := (band (row w k) b).b2
def A (w : Fin 11) (k : ℕ) (b : Fin 7) : ℕ := T w k b-E w k b
def V (w : Fin 11) (k : ℕ) (b : Fin 7) : ℕ := U w k b+B w k b-3
def H (w : Fin 11) (k : ℕ) (b : Fin 7) : ℕ := (V w k b-1)/B w k b+1
def Span (w : Fin 11) (k : ℕ) (b : Fin 7) : ℕ := V w k b+(V w k b-1)/B w k b*B w k b
def RightPeriod (w : Fin 11) (k : ℕ) (b : Fin 7) : ℕ := Count (V w k b-E w k b-1) (A w k b) (B w k b)
def Middle (w : Fin 11) (k : ℕ) (b : Fin 7) : ℕ := RightPeriod w k b*(V w k b-T w k b)
def Active (w : Fin 11) (k : ℕ) : Finset (Fin 7) := Finset.univ.filter (fun b=>1<E w k b)
def pairJ (w : Fin 11) (k : ℕ) (b c : Fin 7) : ℕ := ((((#[#[#[#[3,3,3,3,3,0,0],#[1,3,3,3,3,0,0],#[0,1,3,3,3,0,0],#[0,0,1,3,3,0,0],#[0,0,0,1,3,0,0],#[0,0,0,0,0,0,0],#[0,0,0,0,0,0,0]],#[#[3,3,3,3,3,3,0],#[1,3,3,3,3,3,0],#[0,1,3,3,3,3,0],#[0,0,1,3,3,3,0],#[0,0,0,1,3,3,0],#[0,0,0,0,1,3,0],#[0,0,0,0,0,0,0]],#[#[3,3,3,3,3,3,0],#[1,3,3,3,3,3,0],#[0,1,3,3,3,3,0],#[0,0,1,3,3,3,0],#[0,0,0,1,3,3,0],#[0,0,0,0,1,3,0],#[0,0,0,0,0,0,0]],#[#[3,3,3,3,3,3,2],#[1,3,3,3,3,3,2],#[0,1,3,3,3,3,2],#[0,0,1,3,3,3,2],#[0,0,0,1,3,3,2],#[0,0,0,0,1,3,2],#[0,0,0,0,0,1,2]],#[#[3,3,3,3,3,3,2],#[1,3,3,3,3,3,2],#[0,1,3,3,3,3,2],#[0,0,1,3,3,3,2],#[0,0,0,1,3,3,2],#[0,0,0,0,1,3,2],#[0,0,0,0,0,1,2]],#[#[3,3,3,3,3,3,2],#[1,3,3,3,3,3,2],#[0,1,3,3,3,3,2],#[0,0,1,3,3,3,2],#[0,0,0,1,3,3,2],#[0,0,0,0,1,3,2],#[0,0,0,0,0,1,2]],#[#[3,3,3,3,3,3,2],#[1,3,3,3,3,3,2],#[0,1,3,3,3,3,2],#[0,0,1,3,3,3,2],#[0,0,0,1,3,3,2],#[0,0,0,0,1,3,2],#[0,0,0,0,0,1,2]],#[#[3,3,3,3,3,3,3],#[1,3,3,3,3,3,3],#[0,1,3,3,3,3,3],#[0,0,1,3,3,3,3],#[0,0,0,1,3,3,3],#[0,0,0,0,1,3,3],#[0,0,0,0,0,1,3]],#[#[3,3,3,3,3,3,3],#[1,3,3,3,3,3,3],#[0,1,3,3,3,3,3],#[0,0,1,3,3,3,3],#[0,0,0,1,3,3,3],#[0,0,0,0,1,3,3],#[0,0,0,0,0,1,3]],#[#[3,3,3,3,3,3,3],#[1,3,3,3,3,3,3],#[0,1,3,3,3,3,3],#[0,0,1,3,3,3,3],#[0,0,0,1,3,3,3],#[0,0,0,0,1,3,3],#[0,0,0,0,0,1,3]],#[#[3,3,3,3,3,3,3],#[1,3,3,3,3,3,3],#[0,1,3,3,3,3,3],#[0,0,1,3,3,3,3],#[0,0,0,1,3,3,3],#[0,0,0,0,1,3,3],#[0,0,0,0,0,1,3]],#[#[3,3,3,3,3,3,3],#[1,3,3,3,3,3,3],#[0,1,3,3,3,3,3],#[0,0,1,3,3,3,3],#[0,0,0,1,3,3,3],#[0,0,0,0,1,3,3],#[0,0,0,0,0,1,3]],#[#[3,3,3,3,3,3,3],#[1,3,3,3,3,3,3],#[0,1,3,3,3,3,3],#[0,0,1,3,3,3,3],#[0,0,0,1,3,3,3],#[0,0,0,0,1,3,3],#[0,0,0,0,0,1,3]],#[#[3,3,3,3,3,3,3],#[1,3,3,3,3,3,3],#[0,1,3,3,3,3,3],#[0,0,1,3,3,3,3],#[0,0,0,1,3,3,3],#[0,0,0,0,1,3,3],#[0,0,0,0,0,1,3]],#[#[3,3,3,3,3,3,3],#[1,3,3,3,3,3,3],#[0,1,3,3,3,3,3],#[0,0,1,3,3,3,3],#[0,0,0,1,3,3,3],#[0,0,0,0,1,3,3],#[0,0,0,0,0,1,3]],#[#[3,3,3,3,3,3,3],#[1,3,3,3,3,3,3],#[0,1,3,3,3,3,3],#[0,0,1,3,3,3,3],#[0,0,0,1,3,3,3],#[0,0,0,0,1,3,3],#[0,0,0,0,0,1,3]],#[#[3,3,3,3,3,3,3],#[1,3,3,3,3,3,3],#[0,1,3,3,3,3,3],#[0,0,1,3,3,3,3],#[0,0,0,1,3,3,3],#[0,0,0,0,1,3,3],#[0,0,0,0,0,1,3]],#[#[4,3,3,3,3,3,3],#[1,3,3,3,3,3,3],#[0,1,3,3,3,3,3],#[0,0,1,3,3,3,3],#[0,0,0,1,3,3,3],#[0,0,0,0,1,3,3],#[0,0,0,0,0,1,3]],#[#[4,3,3,3,3,3,3],#[1,3,3,3,3,3,3],#[0,1,3,3,3,3,3],#[0,0,1,3,3,3,3],#[0,0,0,1,3,3,3],#[0,0,0,0,1,3,3],#[0,0,0,0,0,1,3]],#[#[4,3,3,3,3,3,3],#[1,3,3,3,3,3,3],#[0,1,3,3,3,3,3],#[0,0,1,3,3,3,3],#[0,0,0,1,3,3,3],#[0,0,0,0,1,3,3],#[0,0,0,0,0,1,3]],#[#[4,3,3,3,3,3,3],#[1,3,3,3,3,3,3],#[0,1,3,3,3,3,3],#[0,0,1,3,3,3,3],#[0,0,0,1,3,3,3],#[0,0,0,0,1,3,3],#[0,0,0,0,0,1,3]],#[#[4,3,3,3,3,3,3],#[1,3,3,3,3,3,3],#[0,1,3,3,3,3,3],#[0,0,1,3,3,3,3],#[0,0,0,1,3,3,3],#[0,0,0,0,1,3,3],#[0,0,0,0,0,1,3]],#[#[4,3,3,3,3,3,3],#[1,3,3,3,3,3,3],#[0,1,3,3,3,3,3],#[0,0,1,3,3,3,3],#[0,0,0,1,3,3,3],#[0,0,0,0,1,3,3],#[0,0,0,0,0,1,3]],#[#[4,3,3,3,3,3,3],#[1,3,3,3,3,3,3],#[0,1,3,3,3,3,3],#[0,0,1,3,3,3,3],#[0,0,0,1,3,3,3],#[0,0,0,0,1,3,3],#[0,0,0,0,0,1,3]],#[#[4,3,3,3,3,3,3],#[1,3,3,3,3,3,3],#[0,1,3,3,3,3,3],#[0,0,1,3,3,3,3],#[0,0,0,1,3,3,3],#[0,0,0,0,1,3,3],#[0,0,0,0,0,1,3]],#[#[4,3,3,3,3,3,3],#[2,3,3,3,3,3,3],#[0,1,3,3,3,3,3],#[0,0,1,3,3,3,3],#[0,0,0,1,3,3,3],#[0,0,0,0,1,3,3],#[0,0,0,0,0,1,3]],#[#[4,3,3,3,3,3,3],#[2,3,3,3,3,3,3],#[0,1,3,3,3,3,3],#[0,0,1,3,3,3,3],#[0,0,0,1,3,3,3],#[0,0,0,0,1,3,3],#[0,0,0,0,0,1,3]],#[#[4,3,3,3,3,3,3],#[2,3,3,3,3,3,3],#[0,1,3,3,3,3,3],#[0,0,1,3,3,3,3],#[0,0,0,1,3,3,3],#[0,0,0,0,1,3,3],#[0,0,0,0,0,1,3]],#[#[4,3,3,3,3,3,3],#[2,3,3,3,3,3,3],#[0,1,3,3,3,3,3],#[0,0,1,3,3,3,3],#[0,0,0,1,3,3,3],#[0,0,0,0,1,3,3],#[0,0,0,0,0,1,3]],#[#[4,3,3,3,3,3,3],#[2,3,3,3,3,3,3],#[0,1,3,3,3,3,3],#[0,0,1,3,3,3,3],#[0,0,0,1,3,3,3],#[0,0,0,0,1,3,3],#[0,0,0,0,0,1,3]],#[#[4,3,3,3,3,3,3],#[2,3,3,3,3,3,3],#[0,1,3,3,3,3,3],#[0,0,1,3,3,3,3],#[0,0,0,1,3,3,3],#[0,0,0,0,1,3,3],#[0,0,0,0,0,1,3]],#[#[4,3,3,3,3,3,3],#[2,3,3,3,3,3,3],#[0,1,3,3,3,3,3],#[0,0,1,3,3,3,3],#[0,0,0,1,3,3,3],#[0,0,0,0,1,3,3],#[0,0,0,0,0,1,3]]],#[#[#[3,3,3,3,3,3,0],#[1,3,3,3,3,3,0],#[0,1,3,3,3,3,0],#[0,0,1,3,3,3,0],#[0,0,0,1,3,3,0],#[0,0,0,0,1,3,0],#[0,0,0,0,0,0,0]],#[#[3,3,3,3,3,3,2],#[1,3,3,3,3,3,2],#[0,1,3,3,3,3,2],#[0,0,1,3,3,3,2],#[0,0,0,1,3,3,2],#[0,0,0,0,1,3,2],#[0,0,0,0,0,1,2]],#[#[3,3,3,3,3,3,2],#[1,3,3,3,3,3,2],#[0,1,3,3,3,3,2],#[0,0,1,3,3,3,2],#[0,0,0,1,3,3,2],#[0,0,0,0,1,3,2],#[0,0,0,0,0,1,2]],#[#[3,3,3,3,3,3,3],#[1,3,3,3,3,3,3],#[0,1,3,3,3,3,3],#[0,0,1,3,3,3,3],#[0,0,0,1,3,3,3],#[0,0,0,0,1,3,3],#[0,0,0,0,0,1,3]],#[#[3,3,3,3,3,3,3],#[1,3,3,3,3,3,3],#[0,1,3,3,3,3,3],#[0,0,1,3,3,3,3],#[0,0,0,1,3,3,3],#[0,0,0,0,1,3,3],#[0,0,0,0,0,1,3]],#[#[3,3,3,3,3,3,3],#[1,3,3,3,3,3,3],#[0,1,3,3,3,3,3],#[0,0,1,3,3,3,3],#[0,0,0,1,3,3,3],#[0,0,0,0,1,3,3],#[0,0,0,0,0,1,3]],#[#[3,3,3,3,3,3,3],#[1,3,3,3,3,3,3],#[0,1,3,3,3,3,3],#[0,0,1,3,3,3,3],#[0,0,0,1,3,3,3],#[0,0,0,0,1,3,3],#[0,0,0,0,0,1,3]],#[#[3,3,3,3,3,3,3],#[1,3,3,3,3,3,3],#[0,1,3,3,3,3,3],#[0,0,1,3,3,3,3],#[0,0,0,1,3,3,3],#[0,0,0,0,1,3,3],#[0,0,0,0,0,1,3]],#[#[3,3,3,3,3,3,3],#[1,3,3,3,3,3,3],#[0,1,3,3,3,3,3],#[0,0,1,3,3,3,3],#[0,0,0,1,3,3,3],#[0,0,0,0,1,3,3],#[0,0,0,0,0,1,3]],#[#[4,3,3,3,3,3,3],#[1,3,3,3,3,3,3],#[0,1,3,3,3,3,3],#[0,0,1,3,3,3,3],#[0,0,0,1,3,3,3],#[0,0,0,0,1,3,3],#[0,0,0,0,0,1,3]],#[#[4,3,3,3,3,3,3],#[1,3,3,3,3,3,3],#[0,1,3,3,3,3,3],#[0,0,1,3,3,3,3],#[0,0,0,1,3,3,3],#[0,0,0,0,1,3,3],#[0,0,0,0,0,1,3]],#[#[4,3,3,3,3,3,3],#[1,3,3,3,3,3,3],#[0,1,3,3,3,3,3],#[0,0,1,3,3,3,3],#[0,0,0,1,3,3,3],#[0,0,0,0,1,3,3],#[0,0,0,0,0,1,3]],#[#[4,3,3,3,3,3,3],#[2,3,3,3,3,3,3],#[0,1,3,3,3,3,3],#[0,0,1,3,3,3,3],#[0,0,0,1,3,3,3],#[0,0,0,0,1,3,3],#[0,0,0,0,0,1,3]],#[#[4,3,3,3,3,3,3],#[2,3,3,3,3,3,3],#[0,1,3,3,3,3,3],#[0,0,1,3,3,3,3],#[0,0,0,1,3,3,3],#[0,0,0,0,1,3,3],#[0,0,0,0,0,1,3]],#[#[4,3,3,3,3,3,3],#[2,3,3,3,3,3,3],#[0,1,3,3,3,3,3],#[0,0,1,3,3,3,3],#[0,0,0,1,3,3,3],#[0,0,0,0,1,3,3],#[0,0,0,0,0,1,3]],#[#[4,3,3,3,3,3,3],#[2,3,3,3,3,3,3],#[0,1,3,3,3,3,3],#[0,0,1,3,3,3,3],#[0,0,0,1,3,3,3],#[0,0,0,0,1,3,3],#[0,0,0,0,0,1,3]]],#[#[#[3,3,3,3,3,3,0],#[1,3,3,3,3,3,0],#[0,1,3,3,3,3,0],#[0,0,1,3,3,3,0],#[0,0,0,1,3,3,0],#[0,0,0,0,1,3,0],#[0,0,0,0,0,0,0]],#[#[3,3,3,3,3,3,2],#[1,3,3,3,3,3,2],#[0,1,3,3,3,3,2],#[0,0,1,3,3,3,2],#[0,0,0,1,3,3,2],#[0,0,0,0,1,3,2],#[0,0,0,0,0,1,2]],#[#[3,3,3,3,3,3,2],#[1,3,3,3,3,3,2],#[0,1,3,3,3,3,2],#[0,0,1,3,3,3,2],#[0,0,0,1,3,3,2],#[0,0,0,0,1,3,2],#[0,0,0,0,0,1,2]],#[#[3,3,3,3,3,3,3],#[1,3,3,3,3,3,3],#[0,1,3,3,3,3,3],#[0,0,1,3,3,3,3],#[0,0,0,1,3,3,3],#[0,0,0,0,1,3,3],#[0,0,0,0,0,1,3]],#[#[3,3,3,3,3,3,3],#[1,3,3,3,3,3,3],#[0,1,3,3,3,3,3],#[0,0,1,3,3,3,3],#[0,0,0,1,3,3,3],#[0,0,0,0,1,3,3],#[0,0,0,0,0,1,3]],#[#[3,3,3,3,3,3,3],#[1,3,3,3,3,3,3],#[0,1,3,3,3,3,3],#[0,0,1,3,3,3,3],#[0,0,0,1,3,3,3],#[0,0,0,0,1,3,3],#[0,0,0,0,0,1,3]],#[#[3,3,3,3,3,3,3],#[1,3,3,3,3,3,3],#[0,1,3,3,3,3,3],#[0,0,1,3,3,3,3],#[0,0,0,1,3,3,3],#[0,0,0,0,1,3,3],#[0,0,0,0,0,1,3]],#[#[3,3,3,3,3,3,3],#[1,3,3,3,3,3,3],#[0,1,3,3,3,3,3],#[0,0,1,3,3,3,3],#[0,0,0,1,3,3,3],#[0,0,0,0,1,3,3],#[0,0,0,0,0,1,3]],#[#[3,3,3,3,3,3,3],#[1,3,3,3,3,3,3],#[0,1,3,3,3,3,3],#[0,0,1,3,3,3,3],#[0,0,0,1,3,3,3],#[0,0,0,0,1,3,3],#[0,0,0,0,0,1,3]],#[#[4,3,3,3,3,3,3],#[1,3,3,3,3,3,3],#[0,1,3,3,3,3,3],#[0,0,1,3,3,3,3],#[0,0,0,1,3,3,3],#[0,0,0,0,1,3,3],#[0,0,0,0,0,1,3]],#[#[4,3,3,3,3,3,3],#[1,3,3,3,3,3,3],#[0,1,3,3,3,3,3],#[0,0,1,3,3,3,3],#[0,0,0,1,3,3,3],#[0,0,0,0,1,3,3],#[0,0,0,0,0,1,3]],#[#[4,3,3,3,3,3,3],#[1,3,3,3,3,3,3],#[0,1,3,3,3,3,3],#[0,0,1,3,3,3,3],#[0,0,0,1,3,3,3],#[0,0,0,0,1,3,3],#[0,0,0,0,0,1,3]],#[#[4,3,3,3,3,3,3],#[2,3,3,3,3,3,3],#[0,1,3,3,3,3,3],#[0,0,1,3,3,3,3],#[0,0,0,1,3,3,3],#[0,0,0,0,1,3,3],#[0,0,0,0,0,1,3]],#[#[4,3,3,3,3,3,3],#[2,3,3,3,3,3,3],#[0,1,3,3,3,3,3],#[0,0,1,3,3,3,3],#[0,0,0,1,3,3,3],#[0,0,0,0,1,3,3],#[0,0,0,0,0,1,3]],#[#[4,3,3,3,3,3,3],#[2,3,3,3,3,3,3],#[0,1,3,3,3,3,3],#[0,0,1,3,3,3,3],#[0,0,0,1,3,3,3],#[0,0,0,0,1,3,3],#[0,0,0,0,0,1,3]],#[#[4,3,3,3,3,3,3],#[2,3,3,3,3,3,3],#[0,1,3,3,3,3,3],#[0,0,1,3,3,3,3],#[0,0,0,1,3,3,3],#[0,0,0,0,1,3,3],#[0,0,0,0,0,1,3]]],#[#[#[3,3,3,3,3,3,0],#[1,3,3,3,3,3,0],#[0,1,3,3,3,3,0],#[0,0,1,3,3,3,0],#[0,0,0,1,3,3,0],#[0,0,0,0,1,3,0],#[0,0,0,0,0,0,0]],#[#[3,3,3,3,3,3,2],#[1,3,3,3,3,3,2],#[0,1,3,3,3,3,2],#[0,0,1,3,3,3,2],#[0,0,0,1,3,3,2],#[0,0,0,0,1,3,2],#[0,0,0,0,0,1,2]],#[#[3,3,3,3,3,3,2],#[1,3,3,3,3,3,2],#[0,1,3,3,3,3,2],#[0,0,1,3,3,3,2],#[0,0,0,1,3,3,2],#[0,0,0,0,1,3,2],#[0,0,0,0,0,1,2]],#[#[3,3,3,3,3,3,3],#[1,3,3,3,3,3,3],#[0,1,3,3,3,3,3],#[0,0,1,3,3,3,3],#[0,0,0,1,3,3,3],#[0,0,0,0,1,3,3],#[0,0,0,0,0,1,3]],#[#[3,3,3,3,3,3,3],#[1,3,3,3,3,3,3],#[0,1,3,3,3,3,3],#[0,0,1,3,3,3,3],#[0,0,0,1,3,3,3],#[0,0,0,0,1,3,3],#[0,0,0,0,0,1,3]],#[#[3,3,3,3,3,3,3],#[1,3,3,3,3,3,3],#[0,1,3,3,3,3,3],#[0,0,1,3,3,3,3],#[0,0,0,1,3,3,3],#[0,0,0,0,1,3,3],#[0,0,0,0,0,1,3]],#[#[3,3,3,3,3,3,3],#[1,3,3,3,3,3,3],#[0,1,3,3,3,3,3],#[0,0,1,3,3,3,3],#[0,0,0,1,3,3,3],#[0,0,0,0,1,3,3],#[0,0,0,0,0,1,3]],#[#[3,3,3,3,3,3,3],#[1,3,3,3,3,3,3],#[0,1,3,3,3,3,3],#[0,0,1,3,3,3,3],#[0,0,0,1,3,3,3],#[0,0,0,0,1,3,3],#[0,0,0,0,0,1,3]],#[#[3,3,3,3,3,3,3],#[1,3,3,3,3,3,3],#[0,1,3,3,3,3,3],#[0,0,1,3,3,3,3],#[0,0,0,1,3,3,3],#[0,0,0,0,1,3,3],#[0,0,0,0,0,1,3]],#[#[4,3,3,3,3,3,3],#[1,3,3,3,3,3,3],#[0,1,3,3,3,3,3],#[0,0,1,3,3,3,3],#[0,0,0,1,3,3,3],#[0,0,0,0,1,3,3],#[0,0,0,0,0,1,3]],#[#[4,3,3,3,3,3,3],#[1,3,3,3,3,3,3],#[0,1,3,3,3,3,3],#[0,0,1,3,3,3,3],#[0,0,0,1,3,3,3],#[0,0,0,0,1,3,3],#[0,0,0,0,0,1,3]],#[#[4,3,3,3,3,3,3],#[1,3,3,3,3,3,3],#[0,1,3,3,3,3,3],#[0,0,1,3,3,3,3],#[0,0,0,1,3,3,3],#[0,0,0,0,1,3,3],#[0,0,0,0,0,1,3]],#[#[4,3,3,3,3,3,3],#[2,3,3,3,3,3,3],#[0,1,3,3,3,3,3],#[0,0,1,3,3,3,3],#[0,0,0,1,3,3,3],#[0,0,0,0,1,3,3],#[0,0,0,0,0,1,3]],#[#[4,3,3,3,3,3,3],#[2,3,3,3,3,3,3],#[0,1,3,3,3,3,3],#[0,0,1,3,3,3,3],#[0,0,0,1,3,3,3],#[0,0,0,0,1,3,3],#[0,0,0,0,0,1,3]],#[#[4,3,3,3,3,3,3],#[2,3,3,3,3,3,3],#[0,1,3,3,3,3,3],#[0,0,1,3,3,3,3],#[0,0,0,1,3,3,3],#[0,0,0,0,1,3,3],#[0,0,0,0,0,1,3]],#[#[4,3,3,3,3,3,3],#[2,3,3,3,3,3,3],#[0,1,3,3,3,3,3],#[0,0,1,3,3,3,3],#[0,0,0,1,3,3,3],#[0,0,0,0,1,3,3],#[0,0,0,0,0,1,3]]],#[#[#[3,3,3,3,3,3,2],#[1,3,3,3,3,3,2],#[0,1,3,3,3,3,2],#[0,0,1,3,3,3,2],#[0,0,0,1,3,3,2],#[0,0,0,0,1,3,2],#[0,0,0,0,0,1,2]],#[#[3,3,3,3,3,3,3],#[1,3,3,3,3,3,3],#[0,1,3,3,3,3,3],#[0,0,1,3,3,3,3],#[0,0,0,1,3,3,3],#[0,0,0,0,1,3,3],#[0,0,0,0,0,1,3]],#[#[3,3,3,3,3,3,3],#[1,3,3,3,3,3,3],#[0,1,3,3,3,3,3],#[0,0,1,3,3,3,3],#[0,0,0,1,3,3,3],#[0,0,0,0,1,3,3],#[0,0,0,0,0,1,3]],#[#[3,3,3,3,3,3,3],#[1,3,3,3,3,3,3],#[0,1,3,3,3,3,3],#[0,0,1,3,3,3,3],#[0,0,0,1,3,3,3],#[0,0,0,0,1,3,3],#[0,0,0,0,0,1,3]],#[#[4,3,3,3,3,3,3],#[1,3,3,3,3,3,3],#[0,1,3,3,3,3,3],#[0,0,1,3,3,3,3],#[0,0,0,1,3,3,3],#[0,0,0,0,1,3,3],#[0,0,0,0,0,1,3]],#[#[4,3,3,3,3,3,3],#[1,3,3,3,3,3,3],#[0,1,3,3,3,3,3],#[0,0,1,3,3,3,3],#[0,0,0,1,3,3,3],#[0,0,0,0,1,3,3],#[0,0,0,0,0,1,3]],#[#[4,3,3,3,3,3,3],#[2,3,3,3,3,3,3],#[0,1,3,3,3,3,3],#[0,0,1,3,3,3,3],#[0,0,0,1,3,3,3],#[0,0,0,0,1,3,3],#[0,0,0,0,0,1,3]],#[#[4,3,3,3,3,3,3],#[2,3,3,3,3,3,3],#[0,1,3,3,3,3,3],#[0,0,1,3,3,3,3],#[0,0,0,1,3,3,3],#[0,0,0,0,1,3,3],#[0,0,0,0,0,1,3]]],#[#[#[3,3,3,3,3,3,2],#[1,3,3,3,3,3,2],#[0,1,3,3,3,3,2],#[0,0,1,3,3,3,2],#[0,0,0,1,3,3,2],#[0,0,0,0,1,3,2],#[0,0,0,0,0,1,2]],#[#[3,3,3,3,3,3,3],#[1,3,3,3,3,3,3],#[0,1,3,3,3,3,3],#[0,0,1,3,3,3,3],#[0,0,0,1,3,3,3],#[0,0,0,0,1,3,3],#[0,0,0,0,0,1,3]],#[#[3,3,3,3,3,3,3],#[1,3,3,3,3,3,3],#[0,1,3,3,3,3,3],#[0,0,1,3,3,3,3],#[0,0,0,1,3,3,3],#[0,0,0,0,1,3,3],#[0,0,0,0,0,1,3]],#[#[3,3,3,3,3,3,3],#[1,3,3,3,3,3,3],#[0,1,3,3,3,3,3],#[0,0,1,3,3,3,3],#[0,0,0,1,3,3,3],#[0,0,0,0,1,3,3],#[0,0,0,0,0,1,3]],#[#[4,3,3,3,3,3,3],#[1,3,3,3,3,3,3],#[0,1,3,3,3,3,3],#[0,0,1,3,3,3,3],#[0,0,0,1,3,3,3],#[0,0,0,0,1,3,3],#[0,0,0,0,0,1,3]],#[#[4,3,3,3,3,3,3],#[1,3,3,3,3,3,3],#[0,1,3,3,3,3,3],#[0,0,1,3,3,3,3],#[0,0,0,1,3,3,3],#[0,0,0,0,1,3,3],#[0,0,0,0,0,1,3]],#[#[4,3,3,3,3,3,3],#[2,3,3,3,3,3,3],#[0,1,3,3,3,3,3],#[0,0,1,3,3,3,3],#[0,0,0,1,3,3,3],#[0,0,0,0,1,3,3],#[0,0,0,0,0,1,3]],#[#[4,3,3,3,3,3,3],#[2,3,3,3,3,3,3],#[0,1,3,3,3,3,3],#[0,0,1,3,3,3,3],#[0,0,0,1,3,3,3],#[0,0,0,0,1,3,3],#[0,0,0,0,0,1,3]]],#[#[#[3,3,3,3,3,3,2],#[1,3,3,3,3,3,2],#[0,1,3,3,3,3,2],#[0,0,1,3,3,3,2],#[0,0,0,1,3,3,2],#[0,0,0,0,1,3,2],#[0,0,0,0,0,1,2]],#[#[3,3,3,3,3,3,3],#[1,3,3,3,3,3,3],#[0,1,3,3,3,3,3],#[0,0,1,3,3,3,3],#[0,0,0,1,3,3,3],#[0,0,0,0,1,3,3],#[0,0,0,0,0,1,3]],#[#[3,3,3,3,3,3,3],#[1,3,3,3,3,3,3],#[0,1,3,3,3,3,3],#[0,0,1,3,3,3,3],#[0,0,0,1,3,3,3],#[0,0,0,0,1,3,3],#[0,0,0,0,0,1,3]],#[#[3,3,3,3,3,3,3],#[1,3,3,3,3,3,3],#[0,1,3,3,3,3,3],#[0,0,1,3,3,3,3],#[0,0,0,1,3,3,3],#[0,0,0,0,1,3,3],#[0,0,0,0,0,1,3]],#[#[4,3,3,3,3,3,3],#[1,3,3,3,3,3,3],#[0,1,3,3,3,3,3],#[0,0,1,3,3,3,3],#[0,0,0,1,3,3,3],#[0,0,0,0,1,3,3],#[0,0,0,0,0,1,3]],#[#[4,3,3,3,3,3,3],#[1,3,3,3,3,3,3],#[0,1,3,3,3,3,3],#[0,0,1,3,3,3,3],#[0,0,0,1,3,3,3],#[0,0,0,0,1,3,3],#[0,0,0,0,0,1,3]],#[#[4,3,3,3,3,3,3],#[2,3,3,3,3,3,3],#[0,1,3,3,3,3,3],#[0,0,1,3,3,3,3],#[0,0,0,1,3,3,3],#[0,0,0,0,1,3,3],#[0,0,0,0,0,1,3]],#[#[4,3,3,3,3,3,3],#[2,3,3,3,3,3,3],#[0,1,3,3,3,3,3],#[0,0,1,3,3,3,3],#[0,0,0,1,3,3,3],#[0,0,0,0,1,3,3],#[0,0,0,0,0,1,3]]],#[#[#[3,3,3,3,3,3,2],#[1,3,3,3,3,3,2],#[0,1,3,3,3,3,2],#[0,0,1,3,3,3,2],#[0,0,0,1,3,3,2],#[0,0,0,0,1,3,2],#[0,0,0,0,0,1,2]],#[#[3,3,3,3,3,3,3],#[1,3,3,3,3,3,3],#[0,1,3,3,3,3,3],#[0,0,1,3,3,3,3],#[0,0,0,1,3,3,3],#[0,0,0,0,1,3,3],#[0,0,0,0,0,1,3]],#[#[3,3,3,3,3,3,3],#[1,3,3,3,3,3,3],#[0,1,3,3,3,3,3],#[0,0,1,3,3,3,3],#[0,0,0,1,3,3,3],#[0,0,0,0,1,3,3],#[0,0,0,0,0,1,3]],#[#[3,3,3,3,3,3,3],#[1,3,3,3,3,3,3],#[0,1,3,3,3,3,3],#[0,0,1,3,3,3,3],#[0,0,0,1,3,3,3],#[0,0,0,0,1,3,3],#[0,0,0,0,0,1,3]],#[#[4,3,3,3,3,3,3],#[1,3,3,3,3,3,3],#[0,1,3,3,3,3,3],#[0,0,1,3,3,3,3],#[0,0,0,1,3,3,3],#[0,0,0,0,1,3,3],#[0,0,0,0,0,1,3]],#[#[4,3,3,3,3,3,3],#[1,3,3,3,3,3,3],#[0,1,3,3,3,3,3],#[0,0,1,3,3,3,3],#[0,0,0,1,3,3,3],#[0,0,0,0,1,3,3],#[0,0,0,0,0,1,3]],#[#[4,3,3,3,3,3,3],#[2,3,3,3,3,3,3],#[0,1,3,3,3,3,3],#[0,0,1,3,3,3,3],#[0,0,0,1,3,3,3],#[0,0,0,0,1,3,3],#[0,0,0,0,0,1,3]],#[#[4,3,3,3,3,3,3],#[2,3,3,3,3,3,3],#[0,1,3,3,3,3,3],#[0,0,1,3,3,3,3],#[0,0,0,1,3,3,3],#[0,0,0,0,1,3,3],#[0,0,0,0,0,1,3]]],#[#[#[3,3,3,3,3,3,2],#[1,3,3,3,3,3,2],#[0,1,3,3,3,3,2],#[0,0,1,3,3,3,2],#[0,0,0,1,3,3,2],#[0,0,0,0,1,3,2],#[0,0,0,0,0,1,2]],#[#[3,3,3,3,3,3,3],#[1,3,3,3,3,3,3],#[0,1,3,3,3,3,3],#[0,0,1,3,3,3,3],#[0,0,0,1,3,3,3],#[0,0,0,0,1,3,3],#[0,0,0,0,0,1,3]],#[#[3,3,3,3,3,3,3],#[1,3,3,3,3,3,3],#[0,1,3,3,3,3,3],#[0,0,1,3,3,3,3],#[0,0,0,1,3,3,3],#[0,0,0,0,1,3,3],#[0,0,0,0,0,1,3]],#[#[3,3,3,3,3,3,3],#[1,3,3,3,3,3,3],#[0,1,3,3,3,3,3],#[0,0,1,3,3,3,3],#[0,0,0,1,3,3,3],#[0,0,0,0,1,3,3],#[0,0,0,0,0,1,3]],#[#[4,3,3,3,3,3,3],#[1,3,3,3,3,3,3],#[0,1,3,3,3,3,3],#[0,0,1,3,3,3,3],#[0,0,0,1,3,3,3],#[0,0,0,0,1,3,3],#[0,0,0,0,0,1,3]],#[#[4,3,3,3,3,3,3],#[1,3,3,3,3,3,3],#[0,1,3,3,3,3,3],#[0,0,1,3,3,3,3],#[0,0,0,1,3,3,3],#[0,0,0,0,1,3,3],#[0,0,0,0,0,1,3]],#[#[4,3,3,3,3,3,3],#[2,3,3,3,3,3,3],#[0,1,3,3,3,3,3],#[0,0,1,3,3,3,3],#[0,0,0,1,3,3,3],#[0,0,0,0,1,3,3],#[0,0,0,0,0,1,3]],#[#[4,3,3,3,3,3,3],#[2,3,3,3,3,3,3],#[0,1,3,3,3,3,3],#[0,0,1,3,3,3,3],#[0,0,0,1,3,3,3],#[0,0,0,0,1,3,3],#[0,0,0,0,0,1,3]]],#[#[#[3,3,3,3,3,3,3],#[1,3,3,3,3,3,3],#[0,1,3,3,3,3,3],#[0,0,1,3,3,3,3],#[0,0,0,1,3,3,3],#[0,0,0,0,1,3,3],#[0,0,0,0,0,1,3]],#[#[3,3,3,3,3,3,4],#[1,3,3,3,3,3,4],#[0,1,3,3,3,3,4],#[0,0,1,3,3,3,4],#[0,0,0,1,3,3,4],#[0,0,0,0,1,3,4],#[0,0,0,0,0,1,4]],#[#[3,3,3,3,3,3,4],#[1,3,3,3,3,3,4],#[0,1,3,3,3,3,4],#[0,0,1,3,3,3,4],#[0,0,0,1,3,3,4],#[0,0,0,0,1,3,4],#[0,0,0,0,0,1,4]],#[#[3,3,3,3,3,3,4],#[1,3,3,3,3,3,4],#[0,1,3,3,3,3,4],#[0,0,1,3,3,3,4],#[0,0,0,1,3,3,4],#[0,0,0,0,1,3,4],#[0,0,0,0,0,1,4]],#[#[4,3,3,3,3,3,4],#[1,3,3,3,3,3,4],#[0,1,3,3,3,3,4],#[0,0,1,3,3,3,4],#[0,0,0,1,3,3,4],#[0,0,0,0,1,3,4],#[0,0,0,0,0,1,4]],#[#[4,3,3,3,3,3,4],#[1,3,3,3,3,3,4],#[0,1,3,3,3,3,4],#[0,0,1,3,3,3,4],#[0,0,0,1,3,3,4],#[0,0,0,0,1,3,4],#[0,0,0,0,0,1,4]],#[#[4,3,3,3,3,3,4],#[2,3,3,3,3,3,4],#[0,1,3,3,3,3,4],#[0,0,1,3,3,3,4],#[0,0,0,1,3,3,4],#[0,0,0,0,1,3,4],#[0,0,0,0,0,1,4]],#[#[4,3,3,3,3,3,4],#[2,3,3,3,3,3,4],#[0,1,3,3,3,3,4],#[0,0,1,3,3,3,4],#[0,0,0,1,3,3,4],#[0,0,0,0,1,3,4],#[0,0,0,0,0,1,4]]],#[#[#[3,3,3,3,3,3,4],#[1,3,3,3,3,3,4],#[0,1,3,3,3,3,4],#[0,0,1,3,3,3,4],#[0,0,0,1,3,3,4],#[0,0,0,0,1,3,4],#[0,0,0,0,0,1,4]],#[#[3,3,3,3,3,3,4],#[1,3,3,3,3,3,4],#[0,1,3,3,3,3,4],#[0,0,1,3,3,3,4],#[0,0,0,1,3,3,4],#[0,0,0,0,1,3,4],#[0,0,0,0,0,1,4]],#[#[3,3,3,3,3,3,5],#[1,3,3,3,3,3,5],#[0,1,3,3,3,3,5],#[0,0,1,3,3,3,5],#[0,0,0,1,3,3,5],#[0,0,0,0,1,3,5],#[0,0,0,0,0,1,5]],#[#[3,3,3,3,3,3,5],#[1,3,3,3,3,3,5],#[0,1,3,3,3,3,5],#[0,0,1,3,3,3,5],#[0,0,0,1,3,3,5],#[0,0,0,0,1,3,5],#[0,0,0,0,0,1,5]],#[#[4,3,3,3,3,3,5],#[1,3,3,3,3,3,5],#[0,1,3,3,3,3,5],#[0,0,1,3,3,3,5],#[0,0,0,1,3,3,5],#[0,0,0,0,1,3,5],#[0,0,0,0,0,1,5]],#[#[4,3,3,3,3,3,5],#[1,3,3,3,3,3,5],#[0,1,3,3,3,3,5],#[0,0,1,3,3,3,5],#[0,0,0,1,3,3,5],#[0,0,0,0,1,3,5],#[0,0,0,0,0,1,5]],#[#[4,3,3,3,3,3,5],#[2,3,3,3,3,3,5],#[0,1,3,3,3,3,5],#[0,0,1,3,3,3,5],#[0,0,0,1,3,3,5],#[0,0,0,0,1,3,5],#[0,0,0,0,0,1,5]],#[#[4,3,3,3,3,3,5],#[2,3,3,3,3,3,5],#[0,1,3,3,3,3,5],#[0,0,1,3,3,3,5],#[0,0,0,1,3,3,5],#[0,0,0,0,1,3,5],#[0,0,0,0,0,1,5]]]])[w.val]!)[k]!)[b.val]!)[c.val]!
def heavyCeiling (w : Fin 11) (k : ℕ) : ℕ := ((#[#[371,475,495,615,637,638,663,658,683,684,711,671,717,679,704,706,708,734,762,789,790,817,818,820,850,880,907,909,915,944,947,948],#[475,615,638,681,683,671,679,706,733,762,790,820,880,910,944,974],#[475,615,638,658,683,671,679,706,733,739,790,819,880,909,943,947],#[475,615,639,681,683,671,679,706,733,762,790,820,879,910,944,973],#[615,681,671,706,787,820,909,948],#[615,658,671,706,787,819,910,948],#[615,681,671,706,788,820,910,974],#[593,681,671,706,787,820,910,948],#[595,684,689,724,806,839,929,969],#[642,754,789,824,908,942,1035,1075],#[689,812,910,946,1031,1065,1160,1200]])[w.val]!)[k]!

def HeavyRat (w : Fin 11) (k : ℕ) : ℚ :=
  ((row w k).e : ℚ)*(∑b∈Active w k,(H w k b : ℚ)/(A w k b : ℚ))+
    (∑b∈Active w k,∑c∈Active w k,(H w k b : ℚ)*
      (((pairJ w k b c : ℕ) : ℚ)*(173287/250000)+
        ((Span w k c : ℚ)/(max (A w k b) (A w k c) : ℚ))/(2 : ℚ)^(pairJ w k b c)+
          1/(max (A w k b) (A w k c) : ℚ)))+
    ∑b∈Active w k,(Middle w k b : ℚ)/(A w k b : ℚ)

def Facts (w : Fin 11) : Prop := ∀i : Fin (count w),HeavyRat w i.val≤(heavyCeiling w i.val : ℚ)
instance (w : Fin 11) : Decidable (Facts w) := by unfold Facts;infer_instance
private theorem heavy_row_00_000 : HeavyRat 0 0 ≤ (heavyCeiling 0 0 : ℚ) := by decide +kernel

private theorem heavy_row_00_001 : HeavyRat 0 1 ≤ (heavyCeiling 0 1 : ℚ) := by decide +kernel

private theorem heavy_row_00_002 : HeavyRat 0 2 ≤ (heavyCeiling 0 2 : ℚ) := by decide +kernel

private theorem heavy_row_00_003 : HeavyRat 0 3 ≤ (heavyCeiling 0 3 : ℚ) := by decide +kernel

private theorem heavy_row_00_004 : HeavyRat 0 4 ≤ (heavyCeiling 0 4 : ℚ) := by decide +kernel

private theorem heavy_row_00_005 : HeavyRat 0 5 ≤ (heavyCeiling 0 5 : ℚ) := by decide +kernel

private theorem heavy_row_00_006 : HeavyRat 0 6 ≤ (heavyCeiling 0 6 : ℚ) := by decide +kernel

private theorem heavy_row_00_007 : HeavyRat 0 7 ≤ (heavyCeiling 0 7 : ℚ) := by decide +kernel

private theorem heavy_row_00_008 : HeavyRat 0 8 ≤ (heavyCeiling 0 8 : ℚ) := by decide +kernel

private theorem heavy_row_00_009 : HeavyRat 0 9 ≤ (heavyCeiling 0 9 : ℚ) := by decide +kernel

private theorem heavy_row_00_010 : HeavyRat 0 10 ≤ (heavyCeiling 0 10 : ℚ) := by decide +kernel

private theorem heavy_row_00_011 : HeavyRat 0 11 ≤ (heavyCeiling 0 11 : ℚ) := by decide +kernel

private theorem heavy_row_00_012 : HeavyRat 0 12 ≤ (heavyCeiling 0 12 : ℚ) := by decide +kernel

private theorem heavy_row_00_013 : HeavyRat 0 13 ≤ (heavyCeiling 0 13 : ℚ) := by decide +kernel

private theorem heavy_row_00_014 : HeavyRat 0 14 ≤ (heavyCeiling 0 14 : ℚ) := by decide +kernel

private theorem heavy_row_00_015 : HeavyRat 0 15 ≤ (heavyCeiling 0 15 : ℚ) := by decide +kernel

private theorem heavy_row_00_016 : HeavyRat 0 16 ≤ (heavyCeiling 0 16 : ℚ) := by decide +kernel

private theorem heavy_row_00_017 : HeavyRat 0 17 ≤ (heavyCeiling 0 17 : ℚ) := by decide +kernel

private theorem heavy_row_00_018 : HeavyRat 0 18 ≤ (heavyCeiling 0 18 : ℚ) := by decide +kernel

private theorem heavy_row_00_019 : HeavyRat 0 19 ≤ (heavyCeiling 0 19 : ℚ) := by decide +kernel

private theorem heavy_row_00_020 : HeavyRat 0 20 ≤ (heavyCeiling 0 20 : ℚ) := by decide +kernel

private theorem heavy_row_00_021 : HeavyRat 0 21 ≤ (heavyCeiling 0 21 : ℚ) := by decide +kernel

private theorem heavy_row_00_022 : HeavyRat 0 22 ≤ (heavyCeiling 0 22 : ℚ) := by decide +kernel

private theorem heavy_row_00_023 : HeavyRat 0 23 ≤ (heavyCeiling 0 23 : ℚ) := by decide +kernel

private theorem heavy_row_00_024 : HeavyRat 0 24 ≤ (heavyCeiling 0 24 : ℚ) := by decide +kernel

private theorem heavy_row_00_025 : HeavyRat 0 25 ≤ (heavyCeiling 0 25 : ℚ) := by decide +kernel

private theorem heavy_row_00_026 : HeavyRat 0 26 ≤ (heavyCeiling 0 26 : ℚ) := by decide +kernel

private theorem heavy_row_00_027 : HeavyRat 0 27 ≤ (heavyCeiling 0 27 : ℚ) := by decide +kernel

private theorem heavy_row_00_028 : HeavyRat 0 28 ≤ (heavyCeiling 0 28 : ℚ) := by decide +kernel

private theorem heavy_row_00_029 : HeavyRat 0 29 ≤ (heavyCeiling 0 29 : ℚ) := by decide +kernel

private theorem heavy_row_00_030 : HeavyRat 0 30 ≤ (heavyCeiling 0 30 : ℚ) := by decide +kernel

private theorem heavy_row_00_031 : HeavyRat 0 31 ≤ (heavyCeiling 0 31 : ℚ) := by decide +kernel

private theorem heavy_row_01_000 : HeavyRat 1 0 ≤ (heavyCeiling 1 0 : ℚ) := by decide +kernel

private theorem heavy_row_01_001 : HeavyRat 1 1 ≤ (heavyCeiling 1 1 : ℚ) := by decide +kernel

private theorem heavy_row_01_002 : HeavyRat 1 2 ≤ (heavyCeiling 1 2 : ℚ) := by decide +kernel

private theorem heavy_row_01_003 : HeavyRat 1 3 ≤ (heavyCeiling 1 3 : ℚ) := by decide +kernel

private theorem heavy_row_01_004 : HeavyRat 1 4 ≤ (heavyCeiling 1 4 : ℚ) := by decide +kernel

private theorem heavy_row_01_005 : HeavyRat 1 5 ≤ (heavyCeiling 1 5 : ℚ) := by decide +kernel

private theorem heavy_row_01_006 : HeavyRat 1 6 ≤ (heavyCeiling 1 6 : ℚ) := by decide +kernel

private theorem heavy_row_01_007 : HeavyRat 1 7 ≤ (heavyCeiling 1 7 : ℚ) := by decide +kernel

private theorem heavy_row_01_008 : HeavyRat 1 8 ≤ (heavyCeiling 1 8 : ℚ) := by decide +kernel

private theorem heavy_row_01_009 : HeavyRat 1 9 ≤ (heavyCeiling 1 9 : ℚ) := by decide +kernel

private theorem heavy_row_01_010 : HeavyRat 1 10 ≤ (heavyCeiling 1 10 : ℚ) := by decide +kernel

private theorem heavy_row_01_011 : HeavyRat 1 11 ≤ (heavyCeiling 1 11 : ℚ) := by decide +kernel

private theorem heavy_row_01_012 : HeavyRat 1 12 ≤ (heavyCeiling 1 12 : ℚ) := by decide +kernel

private theorem heavy_row_01_013 : HeavyRat 1 13 ≤ (heavyCeiling 1 13 : ℚ) := by decide +kernel

private theorem heavy_row_01_014 : HeavyRat 1 14 ≤ (heavyCeiling 1 14 : ℚ) := by decide +kernel

private theorem heavy_row_01_015 : HeavyRat 1 15 ≤ (heavyCeiling 1 15 : ℚ) := by decide +kernel

private theorem heavy_row_02_000 : HeavyRat 2 0 ≤ (heavyCeiling 2 0 : ℚ) := by decide +kernel

private theorem heavy_row_02_001 : HeavyRat 2 1 ≤ (heavyCeiling 2 1 : ℚ) := by decide +kernel

private theorem heavy_row_02_002 : HeavyRat 2 2 ≤ (heavyCeiling 2 2 : ℚ) := by decide +kernel

private theorem heavy_row_02_003 : HeavyRat 2 3 ≤ (heavyCeiling 2 3 : ℚ) := by decide +kernel

private theorem heavy_row_02_004 : HeavyRat 2 4 ≤ (heavyCeiling 2 4 : ℚ) := by decide +kernel

private theorem heavy_row_02_005 : HeavyRat 2 5 ≤ (heavyCeiling 2 5 : ℚ) := by decide +kernel

private theorem heavy_row_02_006 : HeavyRat 2 6 ≤ (heavyCeiling 2 6 : ℚ) := by decide +kernel

private theorem heavy_row_02_007 : HeavyRat 2 7 ≤ (heavyCeiling 2 7 : ℚ) := by decide +kernel

private theorem heavy_row_02_008 : HeavyRat 2 8 ≤ (heavyCeiling 2 8 : ℚ) := by decide +kernel

private theorem heavy_row_02_009 : HeavyRat 2 9 ≤ (heavyCeiling 2 9 : ℚ) := by decide +kernel

private theorem heavy_row_02_010 : HeavyRat 2 10 ≤ (heavyCeiling 2 10 : ℚ) := by decide +kernel

private theorem heavy_row_02_011 : HeavyRat 2 11 ≤ (heavyCeiling 2 11 : ℚ) := by decide +kernel

private theorem heavy_row_02_012 : HeavyRat 2 12 ≤ (heavyCeiling 2 12 : ℚ) := by decide +kernel

private theorem heavy_row_02_013 : HeavyRat 2 13 ≤ (heavyCeiling 2 13 : ℚ) := by decide +kernel

private theorem heavy_row_02_014 : HeavyRat 2 14 ≤ (heavyCeiling 2 14 : ℚ) := by decide +kernel

private theorem heavy_row_02_015 : HeavyRat 2 15 ≤ (heavyCeiling 2 15 : ℚ) := by decide +kernel

private theorem heavy_row_03_000 : HeavyRat 3 0 ≤ (heavyCeiling 3 0 : ℚ) := by decide +kernel

private theorem heavy_row_03_001 : HeavyRat 3 1 ≤ (heavyCeiling 3 1 : ℚ) := by decide +kernel

private theorem heavy_row_03_002 : HeavyRat 3 2 ≤ (heavyCeiling 3 2 : ℚ) := by decide +kernel

private theorem heavy_row_03_003 : HeavyRat 3 3 ≤ (heavyCeiling 3 3 : ℚ) := by decide +kernel

private theorem heavy_row_03_004 : HeavyRat 3 4 ≤ (heavyCeiling 3 4 : ℚ) := by decide +kernel

private theorem heavy_row_03_005 : HeavyRat 3 5 ≤ (heavyCeiling 3 5 : ℚ) := by decide +kernel

private theorem heavy_row_03_006 : HeavyRat 3 6 ≤ (heavyCeiling 3 6 : ℚ) := by decide +kernel

private theorem heavy_row_03_007 : HeavyRat 3 7 ≤ (heavyCeiling 3 7 : ℚ) := by decide +kernel

private theorem heavy_row_03_008 : HeavyRat 3 8 ≤ (heavyCeiling 3 8 : ℚ) := by decide +kernel

private theorem heavy_row_03_009 : HeavyRat 3 9 ≤ (heavyCeiling 3 9 : ℚ) := by decide +kernel

private theorem heavy_row_03_010 : HeavyRat 3 10 ≤ (heavyCeiling 3 10 : ℚ) := by decide +kernel

private theorem heavy_row_03_011 : HeavyRat 3 11 ≤ (heavyCeiling 3 11 : ℚ) := by decide +kernel

private theorem heavy_row_03_012 : HeavyRat 3 12 ≤ (heavyCeiling 3 12 : ℚ) := by decide +kernel

private theorem heavy_row_03_013 : HeavyRat 3 13 ≤ (heavyCeiling 3 13 : ℚ) := by decide +kernel

private theorem heavy_row_03_014 : HeavyRat 3 14 ≤ (heavyCeiling 3 14 : ℚ) := by decide +kernel

private theorem heavy_row_03_015 : HeavyRat 3 15 ≤ (heavyCeiling 3 15 : ℚ) := by decide +kernel

private theorem heavy_row_04_000 : HeavyRat 4 0 ≤ (heavyCeiling 4 0 : ℚ) := by decide +kernel

private theorem heavy_row_04_001 : HeavyRat 4 1 ≤ (heavyCeiling 4 1 : ℚ) := by decide +kernel

private theorem heavy_row_04_002 : HeavyRat 4 2 ≤ (heavyCeiling 4 2 : ℚ) := by decide +kernel

private theorem heavy_row_04_003 : HeavyRat 4 3 ≤ (heavyCeiling 4 3 : ℚ) := by decide +kernel

private theorem heavy_row_04_004 : HeavyRat 4 4 ≤ (heavyCeiling 4 4 : ℚ) := by decide +kernel

private theorem heavy_row_04_005 : HeavyRat 4 5 ≤ (heavyCeiling 4 5 : ℚ) := by decide +kernel

private theorem heavy_row_04_006 : HeavyRat 4 6 ≤ (heavyCeiling 4 6 : ℚ) := by decide +kernel

private theorem heavy_row_04_007 : HeavyRat 4 7 ≤ (heavyCeiling 4 7 : ℚ) := by decide +kernel

private theorem heavy_row_05_000 : HeavyRat 5 0 ≤ (heavyCeiling 5 0 : ℚ) := by decide +kernel

private theorem heavy_row_05_001 : HeavyRat 5 1 ≤ (heavyCeiling 5 1 : ℚ) := by decide +kernel

private theorem heavy_row_05_002 : HeavyRat 5 2 ≤ (heavyCeiling 5 2 : ℚ) := by decide +kernel

private theorem heavy_row_05_003 : HeavyRat 5 3 ≤ (heavyCeiling 5 3 : ℚ) := by decide +kernel

private theorem heavy_row_05_004 : HeavyRat 5 4 ≤ (heavyCeiling 5 4 : ℚ) := by decide +kernel

private theorem heavy_row_05_005 : HeavyRat 5 5 ≤ (heavyCeiling 5 5 : ℚ) := by decide +kernel

private theorem heavy_row_05_006 : HeavyRat 5 6 ≤ (heavyCeiling 5 6 : ℚ) := by decide +kernel

private theorem heavy_row_05_007 : HeavyRat 5 7 ≤ (heavyCeiling 5 7 : ℚ) := by decide +kernel

private theorem heavy_row_06_000 : HeavyRat 6 0 ≤ (heavyCeiling 6 0 : ℚ) := by decide +kernel

private theorem heavy_row_06_001 : HeavyRat 6 1 ≤ (heavyCeiling 6 1 : ℚ) := by decide +kernel

private theorem heavy_row_06_002 : HeavyRat 6 2 ≤ (heavyCeiling 6 2 : ℚ) := by decide +kernel

private theorem heavy_row_06_003 : HeavyRat 6 3 ≤ (heavyCeiling 6 3 : ℚ) := by decide +kernel

private theorem heavy_row_06_004 : HeavyRat 6 4 ≤ (heavyCeiling 6 4 : ℚ) := by decide +kernel

private theorem heavy_row_06_005 : HeavyRat 6 5 ≤ (heavyCeiling 6 5 : ℚ) := by decide +kernel

private theorem heavy_row_06_006 : HeavyRat 6 6 ≤ (heavyCeiling 6 6 : ℚ) := by decide +kernel

private theorem heavy_row_06_007 : HeavyRat 6 7 ≤ (heavyCeiling 6 7 : ℚ) := by decide +kernel

private theorem heavy_row_07_000 : HeavyRat 7 0 ≤ (heavyCeiling 7 0 : ℚ) := by decide +kernel

private theorem heavy_row_07_001 : HeavyRat 7 1 ≤ (heavyCeiling 7 1 : ℚ) := by decide +kernel

private theorem heavy_row_07_002 : HeavyRat 7 2 ≤ (heavyCeiling 7 2 : ℚ) := by decide +kernel

private theorem heavy_row_07_003 : HeavyRat 7 3 ≤ (heavyCeiling 7 3 : ℚ) := by decide +kernel

private theorem heavy_row_07_004 : HeavyRat 7 4 ≤ (heavyCeiling 7 4 : ℚ) := by decide +kernel

private theorem heavy_row_07_005 : HeavyRat 7 5 ≤ (heavyCeiling 7 5 : ℚ) := by decide +kernel

private theorem heavy_row_07_006 : HeavyRat 7 6 ≤ (heavyCeiling 7 6 : ℚ) := by decide +kernel

private theorem heavy_row_07_007 : HeavyRat 7 7 ≤ (heavyCeiling 7 7 : ℚ) := by decide +kernel

private theorem heavy_row_08_000 : HeavyRat 8 0 ≤ (heavyCeiling 8 0 : ℚ) := by decide +kernel

private theorem heavy_row_08_001 : HeavyRat 8 1 ≤ (heavyCeiling 8 1 : ℚ) := by decide +kernel

private theorem heavy_row_08_002 : HeavyRat 8 2 ≤ (heavyCeiling 8 2 : ℚ) := by decide +kernel

private theorem heavy_row_08_003 : HeavyRat 8 3 ≤ (heavyCeiling 8 3 : ℚ) := by decide +kernel

private theorem heavy_row_08_004 : HeavyRat 8 4 ≤ (heavyCeiling 8 4 : ℚ) := by decide +kernel

private theorem heavy_row_08_005 : HeavyRat 8 5 ≤ (heavyCeiling 8 5 : ℚ) := by decide +kernel

private theorem heavy_row_08_006 : HeavyRat 8 6 ≤ (heavyCeiling 8 6 : ℚ) := by decide +kernel

private theorem heavy_row_08_007 : HeavyRat 8 7 ≤ (heavyCeiling 8 7 : ℚ) := by decide +kernel

private theorem heavy_row_09_000 : HeavyRat 9 0 ≤ (heavyCeiling 9 0 : ℚ) := by decide +kernel

private theorem heavy_row_09_001 : HeavyRat 9 1 ≤ (heavyCeiling 9 1 : ℚ) := by decide +kernel

private theorem heavy_row_09_002 : HeavyRat 9 2 ≤ (heavyCeiling 9 2 : ℚ) := by decide +kernel

private theorem heavy_row_09_003 : HeavyRat 9 3 ≤ (heavyCeiling 9 3 : ℚ) := by decide +kernel

private theorem heavy_row_09_004 : HeavyRat 9 4 ≤ (heavyCeiling 9 4 : ℚ) := by decide +kernel

private theorem heavy_row_09_005 : HeavyRat 9 5 ≤ (heavyCeiling 9 5 : ℚ) := by decide +kernel

private theorem heavy_row_09_006 : HeavyRat 9 6 ≤ (heavyCeiling 9 6 : ℚ) := by decide +kernel

private theorem heavy_row_09_007 : HeavyRat 9 7 ≤ (heavyCeiling 9 7 : ℚ) := by decide +kernel

private theorem heavy_row_10_000 : HeavyRat 10 0 ≤ (heavyCeiling 10 0 : ℚ) := by decide +kernel

private theorem heavy_row_10_001 : HeavyRat 10 1 ≤ (heavyCeiling 10 1 : ℚ) := by decide +kernel

private theorem heavy_row_10_002 : HeavyRat 10 2 ≤ (heavyCeiling 10 2 : ℚ) := by decide +kernel

private theorem heavy_row_10_003 : HeavyRat 10 3 ≤ (heavyCeiling 10 3 : ℚ) := by decide +kernel

private theorem heavy_row_10_004 : HeavyRat 10 4 ≤ (heavyCeiling 10 4 : ℚ) := by decide +kernel

private theorem heavy_row_10_005 : HeavyRat 10 5 ≤ (heavyCeiling 10 5 : ℚ) := by decide +kernel

private theorem heavy_row_10_006 : HeavyRat 10 6 ≤ (heavyCeiling 10 6 : ℚ) := by decide +kernel

private theorem heavy_row_10_007 : HeavyRat 10 7 ≤ (heavyCeiling 10 7 : ℚ) := by decide +kernel

theorem facts (w : Fin 11) : Facts w := by
  fin_cases w
  · exact (Fin.cases heavy_row_00_000 (Fin.cases heavy_row_00_001 (Fin.cases heavy_row_00_002 (Fin.cases heavy_row_00_003 (Fin.cases heavy_row_00_004 (Fin.cases heavy_row_00_005 (Fin.cases heavy_row_00_006 (Fin.cases heavy_row_00_007 (Fin.cases heavy_row_00_008 (Fin.cases heavy_row_00_009 (Fin.cases heavy_row_00_010 (Fin.cases heavy_row_00_011 (Fin.cases heavy_row_00_012 (Fin.cases heavy_row_00_013 (Fin.cases heavy_row_00_014 (Fin.cases heavy_row_00_015 (Fin.cases heavy_row_00_016 (Fin.cases heavy_row_00_017 (Fin.cases heavy_row_00_018 (Fin.cases heavy_row_00_019 (Fin.cases heavy_row_00_020 (Fin.cases heavy_row_00_021 (Fin.cases heavy_row_00_022 (Fin.cases heavy_row_00_023 (Fin.cases heavy_row_00_024 (Fin.cases heavy_row_00_025 (Fin.cases heavy_row_00_026 (Fin.cases heavy_row_00_027 (Fin.cases heavy_row_00_028 (Fin.cases heavy_row_00_029 (Fin.cases heavy_row_00_030 (Fin.cases heavy_row_00_031 (fun i => Fin.elim0 i)))))))))))))))))))))))))))))))))
  · exact (Fin.cases heavy_row_01_000 (Fin.cases heavy_row_01_001 (Fin.cases heavy_row_01_002 (Fin.cases heavy_row_01_003 (Fin.cases heavy_row_01_004 (Fin.cases heavy_row_01_005 (Fin.cases heavy_row_01_006 (Fin.cases heavy_row_01_007 (Fin.cases heavy_row_01_008 (Fin.cases heavy_row_01_009 (Fin.cases heavy_row_01_010 (Fin.cases heavy_row_01_011 (Fin.cases heavy_row_01_012 (Fin.cases heavy_row_01_013 (Fin.cases heavy_row_01_014 (Fin.cases heavy_row_01_015 (fun i => Fin.elim0 i)))))))))))))))))
  · exact (Fin.cases heavy_row_02_000 (Fin.cases heavy_row_02_001 (Fin.cases heavy_row_02_002 (Fin.cases heavy_row_02_003 (Fin.cases heavy_row_02_004 (Fin.cases heavy_row_02_005 (Fin.cases heavy_row_02_006 (Fin.cases heavy_row_02_007 (Fin.cases heavy_row_02_008 (Fin.cases heavy_row_02_009 (Fin.cases heavy_row_02_010 (Fin.cases heavy_row_02_011 (Fin.cases heavy_row_02_012 (Fin.cases heavy_row_02_013 (Fin.cases heavy_row_02_014 (Fin.cases heavy_row_02_015 (fun i => Fin.elim0 i)))))))))))))))))
  · exact (Fin.cases heavy_row_03_000 (Fin.cases heavy_row_03_001 (Fin.cases heavy_row_03_002 (Fin.cases heavy_row_03_003 (Fin.cases heavy_row_03_004 (Fin.cases heavy_row_03_005 (Fin.cases heavy_row_03_006 (Fin.cases heavy_row_03_007 (Fin.cases heavy_row_03_008 (Fin.cases heavy_row_03_009 (Fin.cases heavy_row_03_010 (Fin.cases heavy_row_03_011 (Fin.cases heavy_row_03_012 (Fin.cases heavy_row_03_013 (Fin.cases heavy_row_03_014 (Fin.cases heavy_row_03_015 (fun i => Fin.elim0 i)))))))))))))))))
  · exact (Fin.cases heavy_row_04_000 (Fin.cases heavy_row_04_001 (Fin.cases heavy_row_04_002 (Fin.cases heavy_row_04_003 (Fin.cases heavy_row_04_004 (Fin.cases heavy_row_04_005 (Fin.cases heavy_row_04_006 (Fin.cases heavy_row_04_007 (fun i => Fin.elim0 i)))))))))
  · exact (Fin.cases heavy_row_05_000 (Fin.cases heavy_row_05_001 (Fin.cases heavy_row_05_002 (Fin.cases heavy_row_05_003 (Fin.cases heavy_row_05_004 (Fin.cases heavy_row_05_005 (Fin.cases heavy_row_05_006 (Fin.cases heavy_row_05_007 (fun i => Fin.elim0 i)))))))))
  · exact (Fin.cases heavy_row_06_000 (Fin.cases heavy_row_06_001 (Fin.cases heavy_row_06_002 (Fin.cases heavy_row_06_003 (Fin.cases heavy_row_06_004 (Fin.cases heavy_row_06_005 (Fin.cases heavy_row_06_006 (Fin.cases heavy_row_06_007 (fun i => Fin.elim0 i)))))))))
  · exact (Fin.cases heavy_row_07_000 (Fin.cases heavy_row_07_001 (Fin.cases heavy_row_07_002 (Fin.cases heavy_row_07_003 (Fin.cases heavy_row_07_004 (Fin.cases heavy_row_07_005 (Fin.cases heavy_row_07_006 (Fin.cases heavy_row_07_007 (fun i => Fin.elim0 i)))))))))
  · exact (Fin.cases heavy_row_08_000 (Fin.cases heavy_row_08_001 (Fin.cases heavy_row_08_002 (Fin.cases heavy_row_08_003 (Fin.cases heavy_row_08_004 (Fin.cases heavy_row_08_005 (Fin.cases heavy_row_08_006 (Fin.cases heavy_row_08_007 (fun i => Fin.elim0 i)))))))))
  · exact (Fin.cases heavy_row_09_000 (Fin.cases heavy_row_09_001 (Fin.cases heavy_row_09_002 (Fin.cases heavy_row_09_003 (Fin.cases heavy_row_09_004 (Fin.cases heavy_row_09_005 (Fin.cases heavy_row_09_006 (Fin.cases heavy_row_09_007 (fun i => Fin.elim0 i)))))))))
  · exact (Fin.cases heavy_row_10_000 (Fin.cases heavy_row_10_001 (Fin.cases heavy_row_10_002 (Fin.cases heavy_row_10_003 (Fin.cases heavy_row_10_004 (Fin.cases heavy_row_10_005 (Fin.cases heavy_row_10_006 (Fin.cases heavy_row_10_007 (fun i => Fin.elim0 i)))))))))
theorem bound (w : Fin 11) (i : Fin (count w)) :
    (HeavyRat w i.val : ℝ)≤(heavyCeiling w i.val : ℝ) := by
  have hh := (Rat.cast_le (K := ℝ)).mpr (facts w i)
  simpa only [Rat.cast_natCast] using hh

def WeightedEta (w : Fin 11) : ℚ :=
  (∑i∈Finset.range (count w),(phi w (i+1)-phi w i)*
    ((IntegerUniformLight209.etaLight w i+heavyCeiling w i : ℕ) : ℚ))/phi w (count w)
def Eta (w : Fin 11) : ℕ := if w.val<4 then 1100 else 2000
theorem eta_numeric (w : Fin 11) : WeightedEta w≤(Eta w : ℚ) := by fin_cases w <;> decide +kernel
theorem eta_budget (w : Fin 11) :
    (∑i∈Finset.range (count w),(psi w (i+1)-psi w i)*
      ((IntegerUniformLight209.etaLight w i+heavyCeiling w i : ℕ) : ℝ))/psi w (count w)≤
        (IntegerRobustPrices209.Eta w : ℝ) := by
  have hh := (Rat.cast_le (K := ℝ)).mpr (eta_numeric w)
  simpa only [WeightedEta,psi,Eta,IntegerRobustPrices209.Eta,Rat.cast_div,Rat.cast_sum,
    Rat.cast_mul,Rat.cast_sub,Rat.cast_natCast] using hh

#print axioms facts
#print axioms bound
#print axioms eta_numeric
#print axioms eta_budget
end
end JSP233.IntegerUniformHeavyData209
