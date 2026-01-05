import Mathlib.Tactic
import Mathlib.Data.Sym.Sym2



-- This file aims to define simple finite graphs and prove
-- Euler's handshake lemma using only basic set theoretic
-- results from mathlib

structure SimpGraph (V : Type*) where
(adj : V → V → Prop)
(symm : Symmetric adj)
(loopless : Irreflexive adj)


def FinSimpGraphSize
  {V : Type*} [Fintype V] (G : SimpGraph V) [∀ v w, Decidable (G.adj v w)] : ℕ :=
  Fintype.card V

def FinSimpGraphNbhd {V : Type*} (G : SimpGraph V) (v : V) : Set V :=
  {u | G.adj v u}


def FinSimpGraph.Deg {V : Type*} [Fintype V] (G : SimpGraph V) (v : V)
[DecidablePred (FinSimpGraphNbhd G v)] : ℕ   :=
 Finset.card (Finset.univ.filter (FinSimpGraphNbhd G v))

 -- In this definition I don't think that DecidablePred is strictly necessary
 -- It should be possible to prove this, which I will try to do later

def FinSimpGraph.Degsum {V : Type*} [Fintype V] (G : SimpGraph V)
[∀ v, DecidablePred (FinSimpGraphNbhd G v)] : ℕ   :=
 ∑ v : V, (FinSimpGraph.Deg G v)

def SimpGraph.Edgeset {V : Type*} (G : SimpGraph V)
[∀ w, DecidablePred (FinSimpGraphNbhd G w)] : Set (V×V) :=
{ (u,v) | G.adj u v }


def SimpGraph.NoEdges {V : Type*} (G : SimpGraph V)
[∀ w, DecidablePred (FinSimpGraphNbhd G w)] [Fintype V] [DecidablePred G.Edgeset] : ℕ :=
Finset.card (Finset.univ.filter (SimpGraph.Edgeset G))



theorem FinSimpGraph.Handshake {V : Type*} [Fintype V] (G : SimpGraph V)
 [∀ v, DecidablePred (FinSimpGraphNbhd G v)] [DecidablePred G.Edgeset]
 :  FinSimpGraph.Degsum (G) = 2*(SimpGraph.NoEdges G) := by
    classical
    rw[SimpGraph.NoEdges]
    generalize hE : (Finset.filter G.Edgeset Finset.univ) = E
    revert hE
    refine Finset.induction_on (E) ?base ?step
    intro hE
    simp
    rw[Degsum]
    rw [Finset.sum_eq_zero_iff]
    simp
    intro i
    rw[Deg]
    rw[Finset.card_eq_zero]
    simp
    rw[FinSimpGraphNbhd]
    intro x
    change ¬ G.adj i x
    by_contra adj
    have nempty : (i,x) ∈ Finset.filter G.Edgeset Finset.univ := by
      simp
      rw[SimpGraph.Edgeset]
      change (G.adj i x)
      exact adj

    have isempty : (i,x) ∉ Finset.filter G.Edgeset Finset.univ := by
        simp [hE]

    contradiction


































  --induction SimpGraph.NoEdges G with
  --| zero =>
  --rw [mul_zero]
  --rw [Degsum]
  --rw [Finset.sum_eq_zero_iff]
  --simp
  --intro i
  --rw[Deg]
  --rw[Finset.card_eq_zero]
  --simp
  --intro x
  --rw[FinSimpGraphNbhd]
