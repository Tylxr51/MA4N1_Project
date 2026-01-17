import Mathlib.Tactic
import Mathlib.Data.Sym.Sym2

-- This file aims to define simple finite graphs and prove
-- Euler's handshake lemma using only basic set theoretic
-- results from mathlib

structure SimpGraph (V : Type*) where
(adj : V → V → Prop)
(symm : Symmetric adj)
(loopless : Irreflexive adj)


def FinSimpGraph.Size
  {V : Type*} [Fintype V] (G : SimpGraph V) [∀ v w, Decidable (G.adj v w)] : ℕ :=
  Fintype.card V

def SimpGraph.Nbhd {V : Type*} (G : SimpGraph V) (v : V) : Set V :=
  {u | G.adj v u}

def SimpGraph.AdjEdgeset {V : Type*} (G : SimpGraph V) (v : V) : Set (V × V) :=
  {(v',u) : V × V | v'=v ∧ u ∈ SimpGraph.Nbhd G v}

noncomputable
instance SimpGraph.FinAdjEdgeset {V : Type*} [Fintype V] (G : SimpGraph V) (v : V) :
  Fintype ↑(G.AdjEdgeset v) := by
  have h1 : (G.AdjEdgeset v).Finite := by
      rw[AdjEdgeset]
      simp
      rw[Nbhd]
      simp
      exact Set.finite_univ.subset (by intro x hx; trivial)
  exact h1.fintype

noncomputable
def SimpGraph.AdjEdgeFinset {V : Type*} [Fintype V] (G : SimpGraph V) (v : V) :
  Finset (V×V) :=
  (G.AdjEdgeset v).toFinset

noncomputable
def FinSimpGraph.Deg {V : Type*} [Fintype V] (G : SimpGraph V) (v : V) : ℕ   :=
 Finset.card (SimpGraph.AdjEdgeFinset G v)

 -- In this definition I don't think that DecidablePred is strictly necessary
 -- It should be possible to prove this, which I will try to do later

noncomputable
def FinSimpGraph.Degsum {V : Type*} [Fintype V] (G : SimpGraph V) : ℕ   :=
 ∑ v : V, (FinSimpGraph.Deg G v)

def SimpGraph.DirEdgeset {V : Type*} (G : SimpGraph V)
 : Set (V×V) :=
{ (u,v) | G.adj u v }

-- I realised after getting into the proof that this definition should
-- take unordered pairs rather than ordered pairs.
-- The goal is to prove the theorem for this definition and then use it to
-- show the correct version

lemma SimpGraph.EdgesetEqUnionAdjEdge {V : Type*} (G : SimpGraph V) :
(⋃ v, SimpGraph.AdjEdgeset G v) = SimpGraph.DirEdgeset G :=  by
  ext
  apply Iff.intro
  · simp
    intro x
    rw[AdjEdgeset]
    rw[Nbhd]
    rw[DirEdgeset]
    simp
    intro h1 h2
    rw[h1]
    exact h2

  simp
  rw[DirEdgeset]
  intro h1
  rename_i x
  have h3 : x ∈ G.AdjEdgeset x.1 := by
    rw[AdjEdgeset]
    simp
    rw[Nbhd]
    simp
    apply h1
  apply Exists.intro _
  apply h3

noncomputable
instance SimpGraph.FinEdgeset {V : Type*} [Fintype V] (G : SimpGraph V) :
  Fintype ↑(G.DirEdgeset) := by
  have h1 : (G.DirEdgeset).Finite := by
      rw[DirEdgeset]
      simp
      exact Set.finite_univ.subset (by intro x hx; trivial)
  exact h1.fintype

noncomputable
def SimpGraph.DirNoEdges {V : Type*} [Fintype V] (G : SimpGraph V) : ℕ :=
Finset.card (SimpGraph.DirEdgeset G).toFinset

lemma SimpGraph.DirEdgesetDisjoint {V : Type*} (G : SimpGraph V) :
∀ ⦃v u : V⦄, v ≠ u → Disjoint (G.AdjEdgeset v) (G.AdjEdgeset u) := by
  intro u v hneq
  rw[Disjoint]
  simp
  intro x h1 h2
  ext
  simp
  by_contra
  rename_i y h4
  have h5 : y ∈ {(v',u) : V × V | v'=v ∧ u ∈ SimpGraph.Nbhd G v} := by
    apply h2
    exact h4
  have hy : y.1 = v ∧ y.2 ∈ G.Nbhd v := by
    simpa
  have h6 : y.1 = v := by
    exact hy.1

  have h7 : y ∈ {(v',w) : V × V | v'=u ∧ w ∈ SimpGraph.Nbhd G u} := by
    apply h1
    exact h4
  have hy' : y.1 = u ∧ y.2 ∈ G.Nbhd u := by
    simpa
  have h8 : y.1 = u := by
    exact hy'.1
  have h9 : u=v := by
    exact h8.symm.trans h6
  contradiction

lemma SimpGraph.DirEdgeFinsetDisjoint {V : Type*} [Fintype V] (G : SimpGraph V) :
∀ ⦃v u : V⦄, v ≠ u → Disjoint (G.AdjEdgeFinset v) (G.AdjEdgeFinset u) := by
  intro u v hneq
  rw[Disjoint]
  simp
  rw[AdjEdgeFinset]
  rw[AdjEdgeFinset]
  simp
  intro x h1 h2
  ext
  simp
  by_contra
  rename_i y h4
  have h5 : y ∈ {(v',u) : V × V | v'=v ∧ u ∈ SimpGraph.Nbhd G v} := by
    apply h2
    exact h4
  have hy : y.1 = v ∧ y.2 ∈ G.Nbhd v := by
    simpa
  have h6 : y.1 = v := by
    exact hy.1

  have h7 : y ∈ {(v',w) : V × V | v'=u ∧ w ∈ SimpGraph.Nbhd G u} := by
    apply h1
    exact h4
  have hy' : y.1 = u ∧ y.2 ∈ G.Nbhd u := by
    simpa
  have h8 : y.1 = u := by
    exact hy'.1
  have h9 : u=v := by
    exact h8.symm.trans h6
  contradiction


theorem SimpGraph.DirHandshake {V : Type*} [Fintype V] (G : SimpGraph V)
: SimpGraph.DirNoEdges G = FinSimpGraph.Degsum G := by
  classical
  rw[DirNoEdges]
  rw[FinSimpGraph.Degsum]
  simp [FinSimpGraph.Deg]
  have hdis : ∀ ⦃v u : V⦄, v ≠ u → Disjoint (G.AdjEdgeFinset v) (G.AdjEdgeFinset u) := by
    exact SimpGraph.DirEdgeFinsetDisjoint G
  have hpdis :
  (↑(Finset.univ : Finset V) : Set V).PairwiseDisjoint G.AdjEdgeFinset := by
    intro u hu v hv hne
    exact hdis hne
  have hsumunion  : Finset.card (Finset.biUnion Finset.univ (G.AdjEdgeFinset))
  = ∑ x, Finset.card (G.AdjEdgeFinset x)  := by
    simpa using
      (Finset.card_biUnion
        (s := (Finset.univ : Finset V))
        (t := G.AdjEdgeFinset)
        (hpdis))
  rw[← hsumunion]
  have hunioneq : Finset.univ.biUnion G.AdjEdgeFinset = G.DirEdgeset.toFinset := by
    apply Finset.ext
    intro a
    simp only [Finset.mem_biUnion, Finset.mem_univ, true_and, Set.mem_toFinset]
    simp [AdjEdgeFinset]
    simp [← SimpGraph.EdgesetEqUnionAdjEdge]
  simp [hunioneq]



-- theorem FinSimpGraph.Handshake {V : Type*} [Fintype V] (G : SimpGraph V)
-- [∀ v, DecidablePred (FinSimpGraph.Nbhd G v)] [DecidablePred G.DirEdgeset]
-- :  FinSimpGraph.Degsum (G) = SimpGraph.NoEdges G := by
--    classical
--    rw[SimpGraph.NoEdges]
--    generalize hE : (Finset.filter G.DirEdgeset Finset.univ) = E
--    revert hE
--    refine Finset.induction_on (E) ?base ?step
--    intro hE
--    simp
--    rw[Degsum]
--    rw [Finset.sum_eq_zero_iff]
--   simp
--    intro i
--    rw[Deg]
--    rw[Finset.card_eq_zero]
--   simp
--    rw[FinSimpGraph.Nbhd]
--    intro x
--    change ¬ G.adj i x
--    by_contra adj
--    have nempty : (i,x) ∈ Finset.filter G.DirEdgeset Finset.univ := by
--      simp
--      rw[SimpGraph.DirEdgeset]
--      change (G.adj i x)
--      exact adj
--
--    have isempty : (i,x) ∉ Finset.filter G.DirEdgeset Finset.univ := by
--        simp [hE]
--
--    contradiction
--
--    simp
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
